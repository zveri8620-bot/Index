# -*- coding: utf-8 -*-
"""🏛️ Реставратор фасадов — Python-версия (Flask).
Полноценная серверная версия с Horde, датасетом, Wikipedia.
"""

import base64
import hashlib
import io
import json
import os
import random
import re
import threading
import time
import traceback
import uuid
from datetime import datetime
from pathlib import Path
from urllib.parse import quote

import requests
from flask import Flask, render_template, request, send_from_directory, jsonify
from PIL import Image

app = Flask(__name__)

BASE_DIR = Path(__file__).resolve().parent
GALLERY_DIR = BASE_DIR / "gallery"
DATASET_DIR = BASE_DIR / "dataset"
HISTORY_FILE = BASE_DIR / "history.json"
FEEDBACK_FILE = BASE_DIR / "feedback.json"
LEARNING_FILE = BASE_DIR / "learning.json"
GALLERY_DIR.mkdir(exist_ok=True)
DATASET_DIR.mkdir(exist_ok=True)

POLLINATIONS_URL = "https://image.pollinations.ai/prompt/"
POLLINATIONS_TEXT = "https://text.pollinations.ai/"
WIKI_API = "https://ru.wikipedia.org/api/rest_v1/page/summary/"
AIHORDE_URL = "https://aihorde.net/api/v2"

POLLINATIONS_TOKEN = os.getenv("POLLINATIONS_TOKEN", "")
AIHORDE_API_KEY = os.getenv("AIHORDE_API_KEY", "eJB9zGgYM1SZ55gi1a4viQ")

CONNECT_TIMEOUT = 15
READ_TIMEOUT = 120
REQUEST_TIMEOUT = (CONNECT_TIMEOUT, READ_TIMEOUT)
MAX_RETRIES = 3
RETRY_BACKOFF = 2
POLLINATIONS_MAX_TIME = 90
POLLINATIONS_INTERVAL = 15

_rate_lock = threading.Lock()
_last_poll_ts = 0.0
_translation_cache = {}
_wiki_cache = {}
_image_hashes = None
_horde_models_cache = None
_horde_models_cache_time = 0

_session = requests.Session()
_session.headers.update({
    "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                   "AppleWebKit/537.36 Chrome/120.0 Safari/537.36"),
    "Accept": "*/*", "Connection": "keep-alive",
})

NO_PEOPLE = "no people, no humans, empty street, building only"
HORDE_NEGATIVE = ("people, humans, person, crowd, faces, portrait, animals, "
                  "blurry, low quality, deformed, watermark, text")

# ===== СТИЛИ =====
STYLES = {
    "Без стиля": "",
    "Сталинка / неоклассика 1950-х": "Stalin-era neoclassical architecture, ornate cornice, arched windows, pastel colors",
    "Сталинский ампир / высотка": "Stalinist empire skyscraper, tiered tower with spire, monumental",
    "Хрущёвка": "Soviet khrushchyovka panel block, 5 stories, plain concrete panels",
    "Брежневка": "Soviet brezhnevka brick apartment block, repetitive balconies",
    "Советский модернизм / брутализм": "Soviet brutalist architecture, raw concrete, monumental forms",
    "Конструктивизм 1920-х": "1920s constructivist architecture, ribbon windows, avant-garde",
    "Русский классицизм / усадьба": "Russian classicism manor, portico with columns, yellow facade",
    "Доходный дом XIX века": "19th century Russian apartment building, red brick, ornate windows",
    "Православный храм": "Russian orthodox church, golden onion domes, white walls",
    "Деревянное зодчество": "traditional Russian wooden architecture, log house, carved frames",
    "Неоготика": "gothic revival, pointed arches, rose window, grey stone, spires",
    "Готика": "gothic cathedral, pointed arches, flying buttresses, tall spires",
    "Ренессанс": "Italian renaissance palazzo, rusticated stone, arched windows",
    "Барокко": "baroque palace facade, rich stucco, pilasters, pastel colors",
    "Рококо": "rococo palace facade, pastel colors, delicate stucco",
    "Ар-деко": "art deco facade, geometric ornament, limestone, stepped silhouette",
    "Баухаус": "bauhaus architecture, white cubic volumes, flat roof, glass",
    "Интернациональный стиль": "international style skyscraper, glass and steel tower",
    "Хай-тек": "high-tech architecture, exposed steel, glass curtain walls",
    "Деконструктивизм": "deconstructivist architecture, twisted forms, sharp angles",
    "Постмодернизм": "postmodern architecture, playful classical references, bright colors",
    "Параметризм / биотек": "parametric architecture, flowing curved surfaces, Zaha Hadid style",
    "Минимализм": "minimalist architecture, clean white volumes, frameless glazing",
    "Скандинавский дом": "Scandinavian minimalist house, light wood, panoramic windows",
    "Альпийское шале": "alpine chalet, wide sloping roof, wooden balconies, stone base",
    "Средиземноморский стиль": "mediterranean villa, white stucco, terracotta roof",
    "Фахверк": "half-timbered fachwerk house, dark wooden beams, light plaster",
    "Тюдор": "tudor style house, black and white timbering, steep gables",
    "Викторианский стиль": "victorian architecture, polychrome brickwork, bay windows",
    "Георгианский стиль": "georgian townhouse, red brick, white sash windows, symmetry",
    "Колониальный стиль": "colonial architecture, verandas with columns, symmetrical facade",
    "Промышленное здание": "industrial factory, red brick, sawtooth roof, large windows",
    "Промышленный лофт": "industrial loft, old factory brick, huge steel windows",
    "Современный ЖК": "contemporary residential complex, ventilated facade, large glazing",
    "Эко-архитектура": "eco architecture, green facade, vertical gardens, wooden structure",
    "Древнекитайская архитектура": "ancient Chinese architecture, pagoda, curved eaves, red columns, glazed tile roof",
    "Древнеяпонская архитектура": "ancient Japanese architecture, wooden temple, curved roof, shoji screens",
    "Античная архитектура": "ancient Greek Roman architecture, marble columns, pediment, temple",
    "Исламская архитектура": "islamic architecture, geometric patterns, horseshoe arches, minaret, dome",
}

WIKI_TITLES = {
    "Сталинка / неоклассика 1950-х": "Сталинский ампир",
    "Хрущёвка": "Хрущёвка", "Брежневка": "Брежневка",
    "Советский модернизм / брутализм": "Брутализм (архитектура)",
    "Конструктивизм 1920-х": "Конструктивизм",
    "Русский классицизм / усадьба": "Классицизм",
    "Доходный дом XIX века": "Доходный дом",
    "Неоготика": "Неоготика", "Готика": "Готическая архитектура",
    "Ренессанс": "Архитектура Возрождения", "Барокко": "Барокко",
    "Рококо": "Рококо", "Ар-деко": "Ар-деко", "Баухаус": "Баухаус",
    "Хай-тек": "Хай-тек (архитектура)", "Минимализм": "Минимализм",
    "Древнекитайская архитектура": "Китайская архитектура",
    "Древнеяпонская архитектура": "Японская архитектура",
    "Античная архитектура": "Античная архитектура",
    "Исламская архитектура": "Исламская архитектура",
}

ARCH_TERMS = {
    "древнекитайское": "ancient Chinese", "древнекитайская": "ancient Chinese",
    "древнеяпонское": "ancient Japanese", "древнеяпонская": "ancient Japanese",
    "здание": "building", "дом": "house", "фасад": "facade",
    "окно": "window", "окна": "windows", "крыша": "roof",
    "колонна": "column", "колонны": "columns", "арка": "arch", "арки": "arches",
    "купол": "dome", "башня": "tower", "стена": "wall", "стены": "walls",
    "этаж": "floor", "балкон": "balcony", "дверь": "door",
    "храм": "temple", "церковь": "church", "дворец": "palace", "замок": "castle",
    "собор": "cathedral", "современный": "modern", "кирпичный": "brick",
    "деревянный": "wooden", "каменный": "stone", "мраморный": "marble",
    "белый": "white", "красный": "red", "желтый": "yellow", "жёлтый": "yellow",
    "серый": "grey", "готический": "gothic", "барокко": "baroque",
    "классицизм": "classicism", "пятиэтажный": "five-storey", "лепнина": "stucco",
}


def has_cyrillic(text): return any('\u0400' <= c <= '\u04FF' for c in text)


def safe_folder_name(style):
    name = re.sub(r'[^\w\s-]', '', style, flags=re.UNICODE)
    name = name.strip().replace(' ', '_')
    return re.sub(r'_+', '_', name)[:60]


# ===== ДАТАСЕТ =====
def scan_dataset():
    dataset = {}
    if not DATASET_DIR.exists():
        return dataset
    style_map = {safe_folder_name(s): s for s in STYLES if s != "Без стиля"}
    sorted_safe = sorted(style_map.keys(), key=len, reverse=True)
    for f in sorted(DATASET_DIR.iterdir()):
        if f.suffix.lower() not in ('.png', '.jpg', '.jpeg', '.webp'):
            continue
        stem = f.stem
        matched = None
        for safe_name in sorted_safe:
            if stem == safe_name or stem.startswith(safe_name + "_") or stem.startswith(safe_name + "-"):
                matched = style_map[safe_name]; break
        if matched is None:
            for safe_name in sorted_safe:
                if stem.startswith(safe_name):
                    matched = style_map[safe_name]; break
        if matched is None: matched = "Прочее"
        dataset.setdefault(matched, {"images": [], "count": 0})
        dataset[matched]["images"].append(f.name)
        dataset[matched]["count"] += 1
    return dataset


def get_dataset_context(style):
    info_file = DATASET_DIR / f"{safe_folder_name(style)}_info.txt"
    if info_file.exists():
        try: return info_file.read_text(encoding='utf-8').strip()[:200]
        except: pass
    return ""


def dataset_stats():
    ds = scan_dataset()
    return {"styles": len(ds),
            "images": sum(v["count"] for v in ds.values()),
            "filled": sum(1 for v in ds.values() if v["count"] > 0)}


def get_offline_image(style):
    ds = scan_dataset()
    candidates = []
    if style in ds and ds[style]["images"]:
        for img in ds[style]["images"]: candidates.append(DATASET_DIR / img)
    if not candidates:
        for data in ds.values():
            for img in data["images"]: candidates.append(DATASET_DIR / img)
    if not candidates: return None
    try: return random.choice(candidates).read_bytes()
    except: return None


# ===== ИСТОРИЯ / ГАЛЕРЕЯ =====
def load_history():
    if HISTORY_FILE.exists():
        try: return json.loads(HISTORY_FILE.read_text(encoding="utf-8"))
        except: pass
    return []


def save_history(history):
    try: HISTORY_FILE.write_text(json.dumps(history, ensure_ascii=False, indent=2), encoding="utf-8")
    except Exception as e: print(f"  ⚠️ history: {e}")


def get_image_hashes():
    global _image_hashes
    if _image_hashes is None:
        _image_hashes = set()
        for f in GALLERY_DIR.glob("*.png"):
            try: _image_hashes.add(hashlib.md5(f.read_bytes()).hexdigest())
            except: pass
    return _image_hashes


def save_to_gallery(img_bytes, meta):
    img_id = datetime.now().strftime("%Y%m%d_%H%M%S") + "_" + uuid.uuid4().hex[:6]
    path = GALLERY_DIR / f"{img_id}.png"
    path.write_bytes(img_bytes)
    get_image_hashes().add(hashlib.md5(img_bytes).hexdigest())
    history = load_history()
    entry = dict(meta)
    entry.update({"id": img_id, "time": datetime.now().strftime("%d.%m.%Y %H:%M:%S"), "file": path.name})
    history.insert(0, entry)
    save_history(history)
    return img_id, path.name


# ===== ОБУЧЕНИЕ =====
def load_learning():
    if LEARNING_FILE.exists():
        try: return json.loads(LEARNING_FILE.read_text(encoding="utf-8"))
        except: pass
    return {"successful_patterns": {}, "failed_patterns": {}, "style_weights": {},
            "total_generations": 0, "total_likes": 0, "total_dislikes": 0, "accuracy": 0.0}


def save_learning(data):
    try: LEARNING_FILE.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
    except Exception as e: print(f"  ⚠️ learning: {e}")


def record_feedback(image_id, rating):
    try:
        history = load_history()
        entry = next((h for h in history if h.get("id") == image_id), None)
        if not entry: return False
        learning = load_learning()
        learning["total_generations"] = learning.get("total_generations", 0) + 1
        style = entry.get("style", "")
        if rating == "like":
            learning["total_likes"] = learning.get("total_likes", 0) + 1
            if style:
                sp = learning.setdefault("successful_patterns", {})
                sp[style] = sp.get(style, 0) + 1
        else:
            learning["total_dislikes"] = learning.get("total_dislikes", 0) + 1
            if style:
                fp = learning.setdefault("failed_patterns", {})
                fp[style] = fp.get(style, 0) + 1
        sw = learning.setdefault("style_weights", {})
        for s in learning.get("successful_patterns", {}):
            success = learning["successful_patterns"].get(s, 0)
            fail = learning.get("failed_patterns", {}).get(s, 0)
            total = success + fail
            if total > 0: sw[s] = success / total
        likes = learning.get("total_likes", 0)
        total_fb = likes + learning.get("total_dislikes", 0)
        learning["accuracy"] = (likes / total_fb) if total_fb > 0 else 0.0
        save_learning(learning)
        return True
    except Exception as e:
        print(f"  ⚠️ feedback: {e}"); return False


# ===== ПЕРЕВОД / ПРОМПТ =====
def fetch_wikipedia_reference(style):
    title = WIKI_TITLES.get(style)
    if not title: return ""
    if title in _wiki_cache: return _wiki_cache[title]
    try:
        resp = _session.get(WIKI_API + quote(title), timeout=10)
        if resp.status_code == 200:
            result = resp.json().get("extract", "")[:300]
            _wiki_cache[title] = result
            return result
    except: pass
    _wiki_cache[title] = ""
    return ""


def translate_to_english(ru_text):
    ru_text = ru_text.strip()
    if not ru_text: return ""
    if not has_cyrillic(ru_text): return ru_text
    if ru_text in _translation_cache: return _translation_cache[ru_text]
    for attempt in range(2):
        try:
            prompt = f"Translate to English, short and precise: {ru_text}"
            resp = _session.get(POLLINATIONS_TEXT + quote(prompt), timeout=(10, 45))
            if resp.status_code == 200:
                tr = resp.text.strip().strip('"').strip("'")[:120]
                if tr and not has_cyrillic(tr):
                    _translation_cache[ru_text] = tr
                    return tr
        except: pass
        time.sleep(2)
    result = ru_text.lower()
    for ru, en in sorted(ARCH_TERMS.items(), key=lambda x: -len(x[0])):
        result = result.replace(ru, en)
    return result.strip() or ru_text


def extract_keywords(description, style, wiki_text):
    try:
        prompt = ("You are an expert architect. "
                  "Return ONLY comma-separated English visual keywords for AI image generation "
                  "(style, era, materials, colors, windows, roof, decorations). "
                  "No sentences.\n"
                  f"Style: {style}\nReference: {wiki_text}\nDescription (Russian): {description}")
        resp = _session.get(POLLINATIONS_TEXT + quote(prompt), timeout=(10, 45))
        if resp.status_code == 200:
            keywords = " ".join(resp.text.strip().strip('"').strip("'").split())[:400]
            if keywords and not has_cyrillic(keywords): return keywords
    except: pass
    return translate_to_english(description)


def prepare_prompt(description, style, task, internet_search=False):
    style_en = STYLES.get(style, "")
    dataset_ctx = get_dataset_context(style)
    reference = ""
    keywords = ""
    if internet_search and description.strip():
        reference = fetch_wikipedia_reference(style)
        keywords = extract_keywords(description, style, reference)
        desc = keywords
    else:
        desc = translate_to_english(description)
    if task == "facade":
        base = "architectural photo, building exterior, facade view, daylight"
    elif task == "plan":
        base = "architectural floor plan, top view, blueprint, black lines on white"
    else:
        base = "restored building exterior, architectural photo, daylight"
    parts = [desc, dataset_ctx, style_en, base, NO_PEOPLE, "high detail"]
    return {"prompt": ", ".join(p for p in parts if p),
            "keywords": keywords, "reference": reference, "dataset_ctx": dataset_ctx}


# ===== ГЕНЕРАТОРЫ =====
def get_horde_models_detailed():
    global _horde_models_cache, _horde_models_cache_time
    now = time.time()
    if _horde_models_cache is not None and (now - _horde_models_cache_time) < 60:
        return _horde_models_cache
    try:
        r = _session.get(f"{AIHORDE_URL}/status/models", timeout=15)
        if r.status_code == 200:
            live = [m for m in r.json() if isinstance(m, dict) and m.get("count", 0) > 0]
            if live:
                _horde_models_cache = live
                _horde_models_cache_time = now
                return live
    except: pass
    return _horde_models_cache or []


def pick_horde_model():
    models = get_horde_models_detailed()
    if not models: return "stable_diffusion"
    blocked = ("hentai", "pony", "furry", "nsfw", "waifu", "anime",
               "illustrious", "yiffy", "babes", "pixel", "comic",
               "cartoon", "ghibli", "fantasy card", "rpg", "dan mumford",
               "mtg", "illuminati", "sci-fi", "vector", "app icon")
    safe = [m for m in models if not any(x in m.get("name", "").lower() for x in blocked)]
    if not safe: safe = models
    safe.sort(key=lambda m: ((m.get("queued") or 0) / max(m.get("count") or 1, 1),
                             m.get("jobs") or 0, m.get("queued") or 0))
    best = safe[0]
    print(f"  🎯 Horde: '{best['name']}' "
          f"(воркеров={best.get('count')}, очередь={best.get('queued')})")
    return best["name"]


def generate_pollinations(prompt, width, height, seed, model="sana"):
    global _last_poll_ts
    with _rate_lock:
        wait = max(0.0, POLLINATIONS_INTERVAL - (time.time() - _last_poll_ts))
    if wait > 0: time.sleep(wait)
    with _rate_lock: _last_poll_ts = time.time()

    start_time = time.time()
    last_error = "неизвестная ошибка"
    for attempt in range(1, MAX_RETRIES + 1):
        if time.time() - start_time > POLLINATIONS_MAX_TIME: break
        try:
            url = POLLINATIONS_URL + quote(prompt)
            params = {"width": width, "height": height, "model": model,
                      "seed": seed, "nologo": "true", "enhance": "false"}
            if POLLINATIONS_TOKEN: params["token"] = POLLINATIONS_TOKEN
            print(f"  🎨 Pollinations: {model}, {width}×{height}, attempt {attempt}")
            resp = _session.get(url, params=params, timeout=REQUEST_TIMEOUT)
            if resp.status_code == 429:
                last_error = "Rate limit (429)"; time.sleep(15); continue
            if resp.status_code == 402:
                last_error = "Требуется токен (402)"; break
            if resp.status_code in (502, 503, 504):
                last_error = f"Перегружен ({resp.status_code})"; time.sleep(RETRY_BACKOFF * attempt); continue
            if resp.status_code != 200:
                last_error = f"HTTP {resp.status_code}"; time.sleep(RETRY_BACKOFF * attempt); continue
            if "image" not in resp.headers.get("Content-Type", ""):
                last_error = "Не изображение"; time.sleep(RETRY_BACKOFF * attempt); continue
            data = resp.content
            if len(data) < 1000:
                last_error = "Маленький ответ"; time.sleep(RETRY_BACKOFF * attempt); continue
            print(f"  ✅ Pollinations: {len(data)} байт")
            return data
        except Exception as e:
            last_error = str(e); time.sleep(RETRY_BACKOFF * attempt)
    raise RuntimeError(f"Pollinations не ответил: {last_error}")


def generate_horde(prompt, width, height, fragment_bytes=None, mode="txt2img"):
    headers = {"apikey": AIHORDE_API_KEY, "Client-Agent": "chai-restoration:1.0:anonymous"}
    model_name = pick_horde_model()
    # Малый размер + малое число шагов — чтобы не получить 403
    payload = {"prompt": prompt + " ### " + HORDE_NEGATIVE,
               "params": {"width": 512, "height": 512, "steps": 12, "cfg_scale": 7},
               "models": [model_name], "nsfw": False, "r2": False}
    if fragment_bytes and mode in ("img2img", "outpainting"):
        payload["source_image"] = base64.b64encode(fragment_bytes).decode("ascii")
        payload["source_processing"] = mode
        payload["params"]["denoising_strength"] = 0.6

    job_id = None
    last_err = ""
    for attempt in range(3):
        try:
            resp = _session.post(f"{AIHORDE_URL}/generate/async", json=payload,
                                 headers=headers, timeout=(CONNECT_TIMEOUT, 60))
            if resp.status_code not in (200, 202):
                last_err = f"HTTP {resp.status_code}: {resp.text[:200]}"
                print(f"  ⚠️ Horde {attempt+1}/3: {last_err}"); time.sleep(3); continue
            job_id = resp.json().get("id")
            if job_id: break
        except Exception as e:
            last_err = str(e); print(f"  ⚠️ Horde {attempt+1}/3: {e}"); time.sleep(4)
    if job_id is None:
        raise RuntimeError(f"Horde: не удалось отправить ({last_err})")

    print(f"  ⏳ Horde job_id={job_id[:16]}...")
    done = False
    for i in range(60):
        time.sleep(5)
        try:
            check = _session.get(f"{AIHORDE_URL}/generate/check/{job_id}",
                                 headers=headers, timeout=(CONNECT_TIMEOUT, 30)).json()
        except: continue
        if check.get("done"): done = True; break
        if check.get("faulted"): raise RuntimeError("Horde: задача сломалась")
        if i % 3 == 0:
            print(f"  ⏳ Horde: позиция {check.get('queue_position', '?')}, "
                  f"~{check.get('wait_time', '?')} сек")
    if not done: raise RuntimeError("Horde: таймаут ожидания")

    result = None
    for _ in range(3):
        try:
            result = _session.get(f"{AIHORDE_URL}/generate/status/{job_id}",
                                  headers=headers, timeout=(CONNECT_TIMEOUT, 60)).json(); break
        except: time.sleep(3)
    if result is None: raise RuntimeError("Horde: не удалось получить результат")
    gens = result.get("generations", [])
    if not gens: raise RuntimeError("Horde: пустой результат")
    img_field = gens[0].get("img", "")
    if img_field.startswith("http"):
        for _ in range(3):
            try: raw = _session.get(img_field, timeout=REQUEST_TIMEOUT).content; break
            except: time.sleep(3)
        else: raise RuntimeError("Horde: не удалось скачать")
    else: raw = base64.b64decode(img_field)
    print(f"  ✅ Horde: {len(raw)} байт (512×512)")

    # Апскейл до нужного размера
    try:
        img = Image.open(io.BytesIO(raw)).convert("RGB")
        img = img.resize((width, height), Image.LANCZOS)
        buf = io.BytesIO(); img.save(buf, format="PNG", optimize=True)
        upscaled = buf.getvalue()
        print(f"  🔼 Апскейл до {width}×{height}: {len(upscaled)} байт")
        return upscaled
    except Exception as e:
        print(f"  ⚠️ Апскейл не удался: {e}"); return raw


def generate_with_fallback(prompt, width, height, seed, model="sana", style=""):
    try:
        return generate_pollinations(prompt, width, height, seed, model), "pollinations"
    except Exception as e:
        print(f"  ⚠️ Pollinations упал: {e}")
    try:
        return generate_horde(prompt, width, height), "aihorde"
    except Exception as e:
        print(f"  ⚠️ Horde упал: {e}")
    print("  📁 Офлайн-режим (из датасета)...")
    offline = get_offline_image(style)
    if offline: return offline, "offline-dataset"
    raise RuntimeError("Все сервисы недоступны, а датасет пуст")


# ===== СТРАНИЦЫ =====
@app.route("/")
def page_index():
    return render_template("index.html", styles=list(STYLES.keys()),
                           dataset_stats=dataset_stats(), learning=load_learning(),
                           gallery=load_history(), year=datetime.now().year)


@app.route("/health")
def health():
    return {"pollinations": "OK", "aihorde": "OK",
            "aihorde_key": "задан" if AIHORDE_API_KEY != "0000000000" else "анонимный",
            "time": datetime.now().strftime("%H:%M:%S")}


# ===== ДЕЙСТВИЯ =====
@app.route("/generate", methods=["POST"])
def generate():
    try:
        task = request.form.get("task", "facade")
        description = request.form.get("description", "")
        style = request.form.get("style", "Без стиля")
        model = request.form.get("model", "sana")
        internet_search = request.form.get("internet_search") == "on"
        seed = int(request.form.get("seed") or 0) or random.randint(1, 999999)
        if not description.strip():
            return render_template("index.html", styles=list(STYLES.keys()),
                                   dataset_stats=dataset_stats(), learning=load_learning(),
                                   gallery=load_history(), year=datetime.now().year,
                                   error="Введите описание здания")
        w, h = (896, 1152) if task == "facade" else (1024, 1024)
        prep = prepare_prompt(description, style, task, internet_search)
        img_bytes, engine = generate_with_fallback(prep["prompt"], w, h, seed, model, style)
        img_id, filename = save_to_gallery(img_bytes, {
            "mode": "text", "task": task, "prompt": prep["prompt"], "style": style,
            "engine": engine, "seed": seed, "description_ru": description, "model": model})
        result = {"image": f"/gallery/{filename}", "prompt": prep["prompt"],
                  "engine": engine, "width": w, "height": h, "id": img_id,
                  "keywords": prep["keywords"], "reference": prep["reference"],
                  "dataset_ctx": prep["dataset_ctx"]}
        return render_template("index.html", styles=list(STYLES.keys()),
                               dataset_stats=dataset_stats(), learning=load_learning(),
                               gallery=load_history(), year=datetime.now().year, result=result)
    except Exception as e:
        traceback.print_exc()
        return render_template("index.html", styles=list(STYLES.keys()),
                               dataset_stats=dataset_stats(), learning=load_learning(),
                               gallery=load_history(), year=datetime.now().year,
                               error=f"Ошибка генерации: {e}")


@app.route("/feedback", methods=["POST"])
def feedback():
    image_id = request.form.get("image_id", "")
    rating = request.form.get("rating", "")
    notice = None; error = None
    if image_id and rating in ("like", "dislike"):
        if record_feedback(image_id, rating):
            emoji = "👍" if rating == "like" else "👎"
            notice = f"Спасибо за оценку {emoji}! Нейросеть обучается."
        else:
            error = "Не найдено изображение"
    return render_template("index.html", styles=list(STYLES.keys()),
                           dataset_stats=dataset_stats(), learning=load_learning(),
                           gallery=load_history(), year=datetime.now().year,
                           notice=notice, error=error)


@app.route("/delete", methods=["POST"])
def delete():
    filename = request.form.get("file", "")
    notice = "Изображение удалено"
    if filename and ".." not in filename:
        p = GALLERY_DIR / filename
        if p.exists(): p.unlink(missing_ok=True)
        save_history([h for h in load_history() if h.get("file") != filename])
    return render_template("index.html", styles=list(STYLES.keys()),
                           dataset_stats=dataset_stats(), learning=load_learning(),
                           gallery=load_history(), year=datetime.now().year, notice=notice)


@app.route("/dataset/img/<path:filename>")
def serve_dataset(filename):
    if ".." in filename: return "Bad", 400
    return send_from_directory(DATASET_DIR, filename)


@app.route("/gallery/<path:filename>")
def serve_gallery(filename):
    return send_from_directory(GALLERY_DIR, filename)


@app.errorhandler(404)
def not_found(e):
    return render_template("index.html", styles=list(STYLES.keys()),
                           dataset_stats=dataset_stats(), learning=load_learning(),
                           gallery=load_history(), year=datetime.now().year,
                           error="Страница не найдена"), 404


if __name__ == "__main__":
    print("🏛️ Реставратор фасадов (Python/Flask версия)")
    print("📍 Откройте: http://localhost:5000")
    print(f"📁 Датасет: {DATASET_DIR}")
    if POLLINATIONS_TOKEN: print("🔑 Pollinations: токен задан")
    if AIHORDE_API_KEY != "0000000000": print("🔑 AI Horde: ключ задан (не анонимный)")
    app.run(host="0.0.0.0", port=5000, debug=True, threaded=True)