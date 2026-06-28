import io
import os
import re
import shutil
import zipfile
import tempfile
import webbrowser
from copy import deepcopy
from functools import lru_cache
from pathlib import Path
from threading import Timer
from xml.etree import ElementTree as ET

from flask import Flask, render_template, request, jsonify, send_file
from werkzeug.exceptions import RequestEntityTooLarge

BASE_DIR = Path(__file__).resolve().parent
MAPPINGS_DIR = BASE_DIR / "mappings"
OUTPUT_DIR = BASE_DIR / "output_docs"
OUTPUT_DIR.mkdir(exist_ok=True)

W_NS = "http://schemas.openxmlformats.org/wordprocessingml/2006/main"
R_NS = "http://schemas.openxmlformats.org/officeDocument/2006/relationships"
XML_NS = "http://www.w3.org/XML/1998/namespace"

NS = {"w": W_NS, "r": R_NS}
ET.register_namespace("w", W_NS)
ET.register_namespace("r", R_NS)

XML_PART_EXCLUDE_PREFIXES = ("theme/", "_rels/", "customXml/")
TAMIL_RE = re.compile(r"[\u0B80-\u0BFF]")


DEFAULT_FONT_CONFIG = {
    "unicode": {
        "doc_font": "Arial Unicode MS",
        "aliases": [
            "arial unicode ms",
            "latha",
            "vijaya",
            "nirmala ui",
            "nirmalaui",
            "tau-marutham",
            "marutham"
        ]
    },
    "bamini": {
        "doc_font": "Bamini",
        "aliases": ["bamini"]
    },
    "vanavil": {
        "doc_font": "VANAVIL-Avvaiyar",
        "aliases": ["vanavil-avvaiyar", "vanavil avvaiyar", "vanavil"]
    },
    "sathayam": {
        "doc_font": "Sathayam",
        "aliases": ["sathayam"]
    },
    "anankuhelv": {
        "doc_font": "Ananku Helv",
        "aliases": ["ananku helv", "anankuhelv"]
    },
    "divya": {
        "doc_font": "divya",
        "aliases": ["divya"]
    }
}

app = Flask(__name__)
app.config["MAX_CONTENT_LENGTH"] = 100 * 1024 * 1024


def norm(s):
    return re.sub(r"[_\-\s]+", "", (s or "").strip().lower())


def parse_js_string(src, start):
    q = src[start]
    i = start + 1
    out = []
    n = len(src)
    escapes = {
        "n": "\n", "r": "\r", "t": "\t", "b": "\b", "f": "\f",
        '"': '"', "'": "'", "\\": "\\", "/": "/"
    }

    while i < n:
        ch = src[i]
        if ch == "\\":
            i += 1
            if i >= n:
                break
            esc = src[i]
            if esc == "u" and i + 4 < n:
                hex_part = src[i + 1:i + 5]
                try:
                    out.append(chr(int(hex_part, 16)))
                    i += 5
                    continue
                except ValueError:
                    out.append("u")
                    i += 1
                    continue
            out.append(escapes.get(esc, esc))
            i += 1
            continue
        if ch == q:
            return "".join(out), i + 1
        out.append(ch)
        i += 1

    raise ValueError("Unterminated JS string")


def parse_js_mapping(path):
    src = Path(path).read_text(encoding="utf-8")
    m = re.search(r"const\s+([A-Za-z0-9_]+)\s*=\s*\{", src)
    if not m:
        raise ValueError(f"Invalid mapping file: {path.name}")

    i = src.find("{", m.end() - 1) + 1
    n = len(src)
    data = {}

    while i < n:
        while i < n and src[i] in " \t\r\n,":
            i += 1
        if i >= n or src[i] == "}":
            break

        if src[i:i + 2] == "//":
            i = src.find("\n", i)
            if i == -1:
                break
            continue

        if src[i] not in ('"', "'"):
            i += 1
            continue

        key, i = parse_js_string(src, i)

        while i < n and src[i] in " \t\r\n":
            i += 1
        if i < n and src[i] == ":":
            i += 1
        while i < n and src[i] in " \t\r\n":
            i += 1

        if i >= n or src[i] not in ('"', "'"):
            raise ValueError(f"Invalid value in {path.name}")

        value, i = parse_js_string(src, i)
        data[key] = value

        while i < n and src[i] not in ",}":
            i += 1
        if i < n and src[i] == ",":
            i += 1

    return data


def create_pattern(mapping):
    keys = sorted(mapping.keys(), key=len, reverse=True)
    escaped_keys = [re.escape(k) for k in keys]
    return re.compile("|".join(escaped_keys)) if escaped_keys else re.compile(r"(?!x)x")


def convert_text_regex(text, mapping, pattern):
    if not text or not mapping:
        return text
    return pattern.sub(lambda m: mapping[m.group(0)], text)


def build_match_index(mapping):
    keys = sorted(mapping.keys(), key=len, reverse=True)
    by_first = {}
    for k in keys:
        if not k:
            continue
        by_first.setdefault(k[0], []).append(k)
    return {
        "keys": keys,
        "by_first": by_first
    }


def convert_text_longest_first(text, mapping, match_index=None):
    if not text or not mapping:
        return text

    if match_index is None:
        match_index = build_match_index(mapping)

    by_first = match_index["by_first"]
    out = []
    i = 0
    n = len(text)

    while i < n:
        candidates = by_first.get(text[i], [])
        matched = None

        for key in candidates:
            if text.startswith(key, i):
                matched = key
                break

        if matched is not None:
            out.append(mapping[matched])
            i += len(matched)
        else:
            out.append(text[i])
            i += 1

    return "".join(out)


def better_parse(a, b):
    if a["raw"] != b["raw"]:
        return a["raw"] < b["raw"]
    if a["converted_chars"] != b["converted_chars"]:
        return a["converted_chars"] > b["converted_chars"]
    if a["tokens"] != b["tokens"]:
        return a["tokens"] < b["tokens"]
    if a["first_key_len"] != b["first_key_len"]:
        return a["first_key_len"] > b["first_key_len"]
    return False


def convert_text_best_parse(text, mapping, match_index=None):
    if not text or not mapping:
        return text

    if match_index is None:
        match_index = build_match_index(mapping)

    by_first = match_index["by_first"]
    n = len(text)

    @lru_cache(maxsize=None)
    def solve(i):
        if i >= n:
            return {
                "raw": 0,
                "converted_chars": 0,
                "tokens": 0,
                "first_key_len": 0,
                "parts": ()
            }

        best = None

        candidates = by_first.get(text[i], [])
        for key in candidates:
            if text.startswith(key, i):
                rest = solve(i + len(key))
                cand = {
                    "raw": rest["raw"],
                    "converted_chars": rest["converted_chars"] + len(key),
                    "tokens": rest["tokens"] + 1,
                    "first_key_len": len(key),
                    "parts": ((mapping[key], True),) + rest["parts"]
                }
                if best is None or better_parse(cand, best):
                    best = cand

        rest = solve(i + 1)
        raw_cand = {
            "raw": rest["raw"] + 1,
            "converted_chars": rest["converted_chars"],
            "tokens": rest["tokens"] + 1,
            "first_key_len": 0,
            "parts": ((text[i], False),) + rest["parts"]
        }

        if best is None or better_parse(raw_cand, best):
            best = raw_cand

        return best

    result = solve(0)
    return "".join(x for x, _ in result["parts"])


def reverse_mapping_first_wins(mapping):
    rev = {}
    for k, v in mapping.items():
        if v not in rev:
            rev[v] = k
    return rev


def safe_filename_part(s):
    s = re.sub(r"[^A-Za-z0-9._-]+", "_", (s or "").strip())
    return s.strip("._") or "file"


class TamilDocxConverter:
    def __init__(self, font_config=None):
        self.font_config = deepcopy(font_config or DEFAULT_FONT_CONFIG)
        self.mappings = {}
        self.mapping_errors = []
        self.base_unicode_maps = {}
        self.reset_style_state()
        self.refresh()

    def reset_style_state(self):
        self.styles_by_id = {}
        self.doc_defaults_rpr = None
        self.theme_fonts = {}
        self.theme_font_lang = {}

    def register_mapping(self, src, dst, mapping, file_label, kind):
        self.mappings[(src.lower(), dst.lower())] = {
            "map": mapping,
            "pattern": create_pattern(mapping),
            "match_index": build_match_index(mapping),
            "file": file_label,
            "kind": kind
        }

    def refresh(self):
        self.mappings = {}
        self.mapping_errors = []
        self.base_unicode_maps = {}
        self.reset_style_state()

        for js_file in sorted(MAPPINGS_DIR.glob("*.js")):
            stem = js_file.stem.lower()
            if not stem.endswith("_to_unicode"):
                continue

            src = stem[:-len("_to_unicode")]

            try:
                mapping = parse_js_mapping(js_file)
                self.base_unicode_maps[src] = {
                    "map": mapping,
                    "file": js_file.name
                }
            except Exception as e:
                self.mapping_errors.append({
                    "file": js_file.name,
                    "error": str(e)
                })

        self.build_all_mappings()

    def parse_theme_fonts(self, temp_root):
        self.theme_fonts = {}
        theme_path = Path(temp_root) / "word" / "theme" / "theme1.xml"
        if not theme_path.exists():
            return

        try:
            tree = ET.parse(theme_path)
            root = tree.getroot()
        except ET.ParseError:
            return

        ns_a = {"a": "http://schemas.openxmlformats.org/drawingml/2006/main"}
        font_scheme = root.find(".//a:themeElements/a:fontScheme", ns_a)
        if font_scheme is None:
            return

        major = font_scheme.find("a:majorFont", ns_a)
        minor = font_scheme.find("a:minorFont", ns_a)

        def latin_typeface(elem):
            if elem is None:
                return None
            latin = elem.find("a:latin", ns_a)
            return latin.get("typeface") if latin is not None else None

        major_latin = latin_typeface(major)
        minor_latin = latin_typeface(minor)

        if major_latin:
            self.theme_fonts["majorAscii"] = major_latin
            self.theme_fonts["majorHAnsi"] = major_latin
            self.theme_fonts["majorBidi"] = major_latin
        if minor_latin:
            self.theme_fonts["minorAscii"] = minor_latin
            self.theme_fonts["minorHAnsi"] = minor_latin
            self.theme_fonts["minorBidi"] = minor_latin

    def parse_settings_theme_lang(self, temp_root):
        self.theme_font_lang = {}
        settings_path = Path(temp_root) / "word" / "settings.xml"
        if not settings_path.exists():
            return

        try:
            tree = ET.parse(settings_path)
            root = tree.getroot()
        except ET.ParseError:
            return

        elem = root.find(f".//{{{W_NS}}}themeFontLang")
        if elem is None:
            return

        for k in ("val", "eastAsia", "bidi"):
            v = elem.get(f"{{{W_NS}}}{k}")
            if v:
                self.theme_font_lang[k] = v

    def parse_styles(self, temp_root):
        self.styles_by_id = {}
        self.doc_defaults_rpr = None

        styles_path = Path(temp_root) / "word" / "styles.xml"
        if not styles_path.exists():
            return

        try:
            tree = ET.parse(styles_path)
            root = tree.getroot()
        except ET.ParseError:
            return

        doc_defaults = root.find(f"{{{W_NS}}}docDefaults")
        if doc_defaults is not None:
            rpr_default = doc_defaults.find(f"{{{W_NS}}}rPrDefault")
            if rpr_default is not None:
                self.doc_defaults_rpr = rpr_default.find(f"{{{W_NS}}}rPr")

        for style in root.findall(f"{{{W_NS}}}style"):
            style_id = style.get(f"{{{W_NS}}}styleId")
            if not style_id:
                continue

            style_type = style.get(f"{{{W_NS}}}type")
            based_on = style.find(f"{{{W_NS}}}basedOn")
            based_on_id = based_on.get(f"{{{W_NS}}}val") if based_on is not None else None

            ppr = style.find(f"{{{W_NS}}}pPr")
            rpr = style.find(f"{{{W_NS}}}rPr")

            self.styles_by_id[style_id] = {
                "id": style_id,
                "type": style_type,
                "based_on": based_on_id,
                "ppr": ppr,
                "rpr": rpr
            }

    def build_all_mappings(self):
        available = dict(self.base_unicode_maps)
        ids = sorted(available.keys())

        for font_id in ids:
            base_map = available[font_id]["map"]
            base_file = available[font_id]["file"]

            self.register_mapping(
                font_id,
                "unicode",
                base_map,
                base_file,
                "base"
            )

            self.register_mapping(
                "unicode",
                font_id,
                reverse_mapping_first_wins(base_map),
                f"[auto-reverse] {base_file}",
                "auto-reverse"
            )

    def known_encodings(self):
        names = {"unicode"}
        names.update(self.font_config.keys())
        names.update(self.base_unicode_maps.keys())
        names.update(a for a, _ in self.mappings.keys())
        names.update(b for _, b in self.mappings.keys())
        return sorted(names)

    def doc_font_for_encoding(self, encoding):
        cfg = self.font_config.get(encoding.lower(), {})
        return cfg.get("doc_font") or encoding

    def doc_font_aliases(self, encoding):
        cfg = self.font_config.get(encoding.lower(), {})
        vals = [cfg.get("doc_font", "")]
        vals.extend(cfg.get("aliases", []))
        return {norm(v) for v in vals if v}

    def font_matches_encoding(self, font_name, encoding):
        if not font_name:
            return False
        return norm(font_name) in self.doc_font_aliases(encoding)

    def prefers_best_parse(self, source_encoding):
        return source_encoding.lower() in {"divya"}

    def get_mapping_entry(self, src, dst):
        return self.mappings.get((src.lower(), dst.lower()))

    def build_pipeline(self, source_encoding, target_encoding):
        s = source_encoding.lower()
        t = target_encoding.lower()

        if s == t:
            raise ValueError("Source and target must be different")

        if s != "unicode" and t != "unicode":
            s_to_unicode = self.get_mapping_entry(s, "unicode")
            unicode_to_t = self.get_mapping_entry("unicode", t)
            if s_to_unicode and unicode_to_t:
                return [
                    (s, "unicode", s_to_unicode),
                    ("unicode", t, unicode_to_t)
                ]

        direct = self.get_mapping_entry(s, t)
        if direct:
            return [(s, t, direct)]

        raise ValueError(f"No mapping path found: {source_encoding} -> {target_encoding}")

    def resolve_theme_font_name(self, rfonts):
        if rfonts is None:
            return None

        for attr in ("asciiTheme", "hAnsiTheme", "csTheme", "eastAsiaTheme"):
            v = rfonts.get(f"{{{W_NS}}}{attr}")
            if v and v in self.theme_fonts:
                return self.theme_fonts[v]
        return None

    def get_font_name_from_rpr(self, rpr):
        if rpr is None:
            return None

        rfonts = rpr.find(f"{{{W_NS}}}rFonts")
        if rfonts is None:
            return None

        for attr in ("ascii", "hAnsi", "cs", "eastAsia"):
            val = rfonts.get(f"{{{W_NS}}}{attr}")
            if val:
                return val

        return self.resolve_theme_font_name(rfonts)

    def get_font_name(self, rpr):
        return self.get_font_name_from_rpr(rpr)

    def set_font(self, rpr, font_name):
        if rpr is None:
            return
        rfonts = rpr.find(f"{{{W_NS}}}rFonts")
        if rfonts is None:
            rfonts = ET.SubElement(rpr, f"{{{W_NS}}}rFonts")

        for attr in ("asciiTheme", "hAnsiTheme", "cstheme", "csTheme", "eastAsiaTheme"):
            qn = f"{{{W_NS}}}{attr}"
            if qn in rfonts.attrib:
                del rfonts.attrib[qn]

        for attr in ("ascii", "hAnsi", "cs", "eastAsia"):
            rfonts.set(f"{{{W_NS}}}{attr}", font_name)

    def get_font_size_vals_from_rpr(self, rpr):
        if rpr is None:
            return (None, None)
        sz = rpr.find(f"{{{W_NS}}}sz")
        szcs = rpr.find(f"{{{W_NS}}}szCs")
        sz_val = sz.get(f"{{{W_NS}}}val") if sz is not None else None
        szcs_val = szcs.get(f"{{{W_NS}}}val") if szcs is not None else None
        return sz_val, szcs_val

    def get_font_size_vals(self, rpr):
        return self.get_font_size_vals_from_rpr(rpr)

    def set_font_size_vals(self, rpr, sz_val=None, szcs_val=None):
        if rpr is None:
            return

        if sz_val:
            sz = rpr.find(f"{{{W_NS}}}sz")
            if sz is None:
                sz = ET.SubElement(rpr, f"{{{W_NS}}}sz")
            sz.set(f"{{{W_NS}}}val", str(sz_val))

        if szcs_val:
            szcs = rpr.find(f"{{{W_NS}}}szCs")
            if szcs is None:
                szcs = ET.SubElement(rpr, f"{{{W_NS}}}szCs")
            szcs.set(f"{{{W_NS}}}val", str(szcs_val))

    def preserve_space(self, t_elem, text):
        if text and (text[:1].isspace() or text[-1:].isspace() or " " in text):
            t_elem.set(f"{{{XML_NS}}}space", "preserve")
        else:
            t_elem.attrib.pop(f"{{{XML_NS}}}space", None)

    def collect_style_chain(self, style_id):
        chain = []
        seen = set()
        current = style_id

        while current and current not in seen:
            seen.add(current)
            style = self.styles_by_id.get(current)
            if not style:
                break
            chain.append(style)
            current = style["based_on"]

        chain.reverse()
        return chain

    def merge_font_info_from_rpr(self, info, rpr):
        if rpr is None:
            return info

        font_name = self.get_font_name_from_rpr(rpr)
        if font_name:
            info["font_name"] = font_name

        sz_val, szcs_val = self.get_font_size_vals_from_rpr(rpr)
        if sz_val:
            info["sz"] = sz_val
        if szcs_val:
            info["szCs"] = szcs_val

        return info

    def get_paragraph_style_id(self, para):
        ppr = para.find(f"{{{W_NS}}}pPr")
        if ppr is None:
            return None
        pstyle = ppr.find(f"{{{W_NS}}}pStyle")
        if pstyle is None:
            return None
        return pstyle.get(f"{{{W_NS}}}val")

    def get_run_style_id(self, run):
        rpr = run.find(f"{{{W_NS}}}rPr")
        if rpr is None:
            return None
        rstyle = rpr.find(f"{{{W_NS}}}rStyle")
        if rstyle is None:
            return None
        return rstyle.get(f"{{{W_NS}}}val")

    def get_effective_run_info(self, para, run):
        info = {"font_name": None, "sz": None, "szCs": None}

        info = self.merge_font_info_from_rpr(info, self.doc_defaults_rpr)

        p_style_id = self.get_paragraph_style_id(para)
        if p_style_id:
            for style in self.collect_style_chain(p_style_id):
                info = self.merge_font_info_from_rpr(info, style.get("rpr"))
                ppr = style.get("ppr")
                if ppr is not None:
                    info = self.merge_font_info_from_rpr(info, ppr.find(f"{{{W_NS}}}rPr"))

        ppr_direct = para.find(f"{{{W_NS}}}pPr")
        if ppr_direct is not None:
            info = self.merge_font_info_from_rpr(info, ppr_direct.find(f"{{{W_NS}}}rPr"))

        r_style_id = self.get_run_style_id(run)
        if r_style_id:
            for style in self.collect_style_chain(r_style_id):
                info = self.merge_font_info_from_rpr(info, style.get("rpr"))

        run_rpr = run.find(f"{{{W_NS}}}rPr")
        info = self.merge_font_info_from_rpr(info, run_rpr)

        return info

    def clone_run_props_only(self, run):
        new_run = ET.Element(f"{{{W_NS}}}r")
        rpr = run.find(f"{{{W_NS}}}rPr")
        if rpr is not None:
            new_run.append(deepcopy(rpr))
        return new_run

    def make_text_run_from_template(self, template_run, text, font_name=None):
        new_run = self.clone_run_props_only(template_run)

        rpr = new_run.find(f"{{{W_NS}}}rPr")
        if rpr is None:
            rpr = ET.Element(f"{{{W_NS}}}rPr")
            new_run.insert(0, rpr)

        if font_name:
            self.set_font(rpr, font_name)

        t = ET.Element(f"{{{W_NS}}}t")
        t.text = text
        self.preserve_space(t, text)
        new_run.append(t)
        return new_run

    def make_tab_run_from_template(self, template_run):
        new_run = self.clone_run_props_only(template_run)
        tab = ET.Element(f"{{{W_NS}}}tab")
        new_run.append(tab)
        return new_run

    def tokenize_run(self, run):
        tokens = []
        for child in list(run):
            if child.tag == f"{{{W_NS}}}rPr":
                continue
            if child.tag == f"{{{W_NS}}}t":
                text = child.text or ""
                if text:
                    tokens.append({"type": "text", "text": text, "run": run})
            elif child.tag == f"{{{W_NS}}}tab":
                tokens.append({"type": "tab", "run": run})
            elif child.tag == f"{{{W_NS}}}br":
                tokens.append({"type": "break", "run": run, "elem": deepcopy(child)})
            else:
                tokens.append({"type": "xml", "run": run, "elem": deepcopy(child)})
        return tokens

    def collect_paragraph_tokens(self, para):
        tokens = []
        runs = []
        for child in list(para):
            if child.tag != f"{{{W_NS}}}r":
                continue
            run_tokens = self.tokenize_run(child)
            if run_tokens:
                runs.append(child)
                tokens.extend(run_tokens)
        return runs, tokens

    def get_plain_paragraph_text(self, para):
        parts = []
        for child in list(para):
            if child.tag != f"{{{W_NS}}}r":
                continue
            for node in list(child):
                if node.tag == f"{{{W_NS}}}t":
                    if node.text:
                        parts.append(node.text)
                elif node.tag == f"{{{W_NS}}}tab":
                    parts.append("\t")
        return "".join(parts)

    def legacy_match_score(self, text, mapping_entry, source_encoding):
        if not text or not mapping_entry:
            return 0, 0, 0.0

        mapping = mapping_entry["map"]
        match_index = mapping_entry.get("match_index") or build_match_index(mapping)
        by_first = match_index["by_first"]

        i = 0
        matched_chars = 0
        token_count = 0
        n = len(text)

        while i < n:
            candidates = by_first.get(text[i], [])
            found = None
            for key in candidates:
                if text.startswith(key, i):
                    found = key
                    break
            if found:
                matched_chars += len(found)
                token_count += 1
                i += len(found)
            else:
                i += 1

        ratio = (matched_chars / n) if n else 0.0
        return matched_chars, token_count, ratio

    def paragraph_looks_like_source_encoding(self, para, source_encoding, pipeline):
        if source_encoding.lower() == "unicode":
            return False

        first_step = pipeline[0][2] if pipeline else None
        if not first_step:
            return False

        text = self.get_plain_paragraph_text(para)
        if not text.strip():
            return False

        matched_chars, token_count, ratio = self.legacy_match_score(
            text, first_step, source_encoding
        )

        if source_encoding.lower() == "divya":
            return matched_chars >= 4 and token_count >= 2 and ratio >= 0.35

        return matched_chars >= 4 and token_count >= 2 and ratio >= 0.40

    def collect_runs_with_flags(self, para, source_encoding, pipeline=None):
        runs = []
        any_convertible = False

        for child in list(para):
            if child.tag != f"{{{W_NS}}}r":
                continue

            effective = self.get_effective_run_info(para, child)
            convertible = self.font_matches_encoding(effective["font_name"], source_encoding)
            if convertible:
                any_convertible = True

            runs.append({
                "run": child,
                "font": effective["font_name"],
                "sz": effective["sz"],
                "szCs": effective["szCs"],
                "convertible": convertible,
                "tokens": self.tokenize_run(child)
            })

        if not any_convertible and pipeline and self.paragraph_looks_like_source_encoding(
            para, source_encoding, pipeline
        ):
            for info in runs:
                if info["tokens"]:
                    info["convertible"] = True

        return runs

    def choose_template_run_for_group(self, run_infos, source_encoding):
        best_run = None
        best_score = None

        for info in run_infos:
            text_len = 0
            for tok in info["tokens"]:
                if tok["type"] == "text":
                    text_len += len(tok["text"])

            score = (
                1 if self.font_matches_encoding(info.get("font"), source_encoding) else 0,
                text_len,
                int(info.get("szCs") or info.get("sz") or 0)
            )

            if best_score is None or score > best_score:
                best_score = score
                best_run = info["run"]

        return best_run or run_infos[0]["run"]

    def split_unicode_segments(self, text, mapping):
        if not text:
            return []

        def kind(ch):
            if TAMIL_RE.search(ch):
                return "convertible"
            if ch == " ":
                return "convertible"
            if ch in mapping:
                return "convertible"
            return "other"

        segments = []
        buf = [text[0]]
        current_kind = kind(text[0])

        for ch in text[1:]:
            k = kind(ch)
            if k == current_kind:
                buf.append(ch)
            else:
                segments.append((current_kind, "".join(buf)))
                buf = [ch]
                current_kind = k

        segments.append((current_kind, "".join(buf)))
        return segments

    def convert_unicode_text_preserving_other(self, text, mapping_entry):
        mapping = mapping_entry["map"]
        pattern = mapping_entry["pattern"]
        segments = self.split_unicode_segments(text, mapping)

        converted_parts = []
        changed_chars = 0

        for kind, seg_text in segments:
            if kind == "convertible":
                converted = convert_text_regex(seg_text, mapping, pattern)
                if converted != seg_text:
                    changed_chars += len(seg_text)
                converted_parts.append(("converted", converted))
            else:
                converted_parts.append(("other", seg_text))

        return converted_parts, changed_chars

    def replace_paragraph_runs(self, para, original_runs, new_runs):
        if not original_runs:
            return False

        parent_children = list(para)
        insert_at = None
        for idx, child in enumerate(parent_children):
            if child is original_runs[0]:
                insert_at = idx
                break

        if insert_at is None:
            return False

        for r in original_runs:
            if r in list(para):
                para.remove(r)

        for nr in reversed(new_runs):
            para.insert(insert_at, nr)

        return True

    def build_preserved_runs_from_original(self, run_infos):
        new_runs = []

        for info in run_infos:
            run = info["run"]
            for tok in info["tokens"]:
                if tok["type"] == "text":
                    new_runs.append(self.make_text_run_from_template(run, tok["text"], None))
                elif tok["type"] == "tab":
                    new_runs.append(self.make_tab_run_from_template(run))
                elif tok["type"] == "break":
                    nr = self.clone_run_props_only(run)
                    nr.append(tok["elem"])
                    new_runs.append(nr)
                elif tok["type"] == "xml":
                    nr = self.clone_run_props_only(run)
                    nr.append(tok["elem"])
                    new_runs.append(nr)

        return new_runs

    def convert_legacy_text_to_unicode(self, text, mapping_entry, source_encoding):
        if self.prefers_best_parse(source_encoding):
            return convert_text_best_parse(
                text,
                mapping_entry["map"],
                mapping_entry.get("match_index")
            )
        return convert_text_longest_first(
            text,
            mapping_entry["map"],
            mapping_entry.get("match_index")
        )

    def convert_via_pipeline_text(self, text, pipeline, source_encoding, target_encoding):
        current = text

        if len(pipeline) == 1:
            s, t, entry = pipeline[0]
            if s != "unicode" and t == "unicode":
                current = self.convert_legacy_text_to_unicode(current, entry, source_encoding)
            elif s == "unicode" and t != "unicode":
                current = convert_text_regex(current, entry["map"], entry["pattern"])
            else:
                current = convert_text_regex(current, entry["map"], entry["pattern"])
            return current

        for s, t, entry in pipeline:
            if s != "unicode" and t == "unicode":
                current = self.convert_legacy_text_to_unicode(current, entry, s)
            elif s == "unicode" and t != "unicode":
                current = convert_text_regex(current, entry["map"], entry["pattern"])
            else:
                current = convert_text_regex(current, entry["map"], entry["pattern"])

        return current

    def build_converted_runs_for_group(
        self, run_infos, pipeline, source_encoding, target_encoding
    ):
        full_text_parts = []
        template_run = self.choose_template_run_for_group(run_infos, source_encoding)

        for info in run_infos:
            for tok in info["tokens"]:
                if tok["type"] == "text":
                    full_text_parts.append(tok["text"])
                elif tok["type"] == "tab":
                    full_text_parts.append("\t")

        if template_run is None:
            return [], 0

        full_text = "".join(full_text_parts)
        converted = self.convert_via_pipeline_text(
            full_text,
            pipeline,
            source_encoding,
            target_encoding
        )

        if converted == full_text:
            return self.build_preserved_runs_from_original(run_infos), 0

        target_doc_font = self.doc_font_for_encoding(target_encoding)
        new_runs = []
        current_text = []

        template_rpr = template_run.find("w:rPr", NS)
        t_sz, t_szcs = self.get_font_size_vals(template_rpr)

        def flush_text():
            nonlocal current_text
            if current_text:
                text_out = "".join(current_text)
                new_run = self.make_text_run_from_template(
                    template_run,
                    text_out,
                    target_doc_font
                )
                rpr = new_run.find(f"{{{W_NS}}}rPr")
                if rpr is None:
                    rpr = ET.Element(f"{{{W_NS}}}rPr")
                    new_run.insert(0, rpr)
                self.set_font(rpr, target_doc_font)
                self.set_font_size_vals(rpr, t_sz, t_szcs or t_sz)
                new_runs.append(new_run)
                current_text = []

        for ch in converted:
            if ch == "\t":
                flush_text()
                tab_run = self.make_tab_run_from_template(template_run)
                tab_rpr = tab_run.find(f"{{{W_NS}}}rPr")
                if tab_rpr is None:
                    tab_rpr = ET.Element(f"{{{W_NS}}}rPr")
                    tab_run.insert(0, tab_rpr)
                self.set_font(tab_rpr, target_doc_font)
                self.set_font_size_vals(tab_rpr, t_sz, t_szcs or t_sz)
                new_runs.append(tab_run)
            else:
                current_text.append(ch)

        flush_text()
        return new_runs, len(full_text)

    def convert_paragraph_legacy_runs(
        self, para, source_encoding, target_encoding, pipeline
    ):
        run_infos = self.collect_runs_with_flags(para, source_encoding, pipeline)
        original_runs = [x["run"] for x in run_infos if x["tokens"]]

        if not original_runs:
            return 0, 0

        grouped = []
        current_group = []
        current_flag = None

        for info in run_infos:
            if not info["tokens"]:
                continue
            flag = info["convertible"]
            if current_group and flag != current_flag:
                grouped.append((current_flag, current_group))
                current_group = [info]
                current_flag = flag
            else:
                if not current_group:
                    current_flag = flag
                current_group.append(info)

        if current_group:
            grouped.append((current_flag, current_group))

        new_runs = []
        changed_chars = 0

        for is_convertible, group in grouped:
            if is_convertible:
                converted_runs, local_changed = self.build_converted_runs_for_group(
                    group, pipeline, source_encoding, target_encoding
                )
                changed_chars += local_changed
                new_runs.extend(converted_runs)
            else:
                new_runs.extend(self.build_preserved_runs_from_original(group))

        if changed_chars == 0:
            return 0, 0

        ok = self.replace_paragraph_runs(para, original_runs, new_runs)
        if not ok:
            return 0, 0

        return 1, changed_chars

    def convert_paragraph(self, para, source_encoding, target_encoding, pipeline):
        if source_encoding.lower() != "unicode":
            return self.convert_paragraph_legacy_runs(
                para, source_encoding, target_encoding, pipeline
            )

        original_runs, tokens = self.collect_paragraph_tokens(para)
        if not original_runs or not tokens:
            return 0, 0

        new_runs = []
        changed_chars = 0
        paragraph_changed = False

        source_doc_font = self.doc_font_for_encoding(source_encoding)
        target_doc_font = self.doc_font_for_encoding(target_encoding)

        for tok in tokens:
            template_run = tok["run"]
            rpr = template_run.find("w:rPr", NS)
            original_font = self.get_font_name(rpr)

            if tok["type"] == "text":
                text = tok["text"]

                parts, changed = self.convert_unicode_text_preserving_other(text, pipeline[0][2])
                changed_chars += changed

                for part_kind, part_text in parts:
                    if part_kind == "converted":
                        current = part_text
                        font_name = target_doc_font
                    else:
                        current = part_text
                        font_name = original_font or source_doc_font

                    new_runs.append(
                        self.make_text_run_from_template(template_run, current, font_name)
                    )

                if changed:
                    paragraph_changed = True

            elif tok["type"] == "tab":
                new_runs.append(self.make_tab_run_from_template(template_run))
            elif tok["type"] == "break":
                new_run = self.clone_run_props_only(template_run)
                new_run.append(tok["elem"])
                new_runs.append(new_run)
            elif tok["type"] == "xml":
                new_run = self.clone_run_props_only(template_run)
                new_run.append(tok["elem"])
                new_runs.append(new_run)

        if not paragraph_changed:
            return 0, 0

        ok = self.replace_paragraph_runs(para, original_runs, new_runs)
        if not ok:
            return 0, 0

        return 1, changed_chars

    def story_parts(self, temp_root):
        word = Path(temp_root) / "word"
        parts = []
        if not word.exists():
            return parts

        for path in sorted(word.rglob("*.xml")):
            rel = path.relative_to(word).as_posix()
            if any(rel.startswith(p) for p in XML_PART_EXCLUDE_PREFIXES):
                continue
            parts.append(path)

        return parts

    def convert_xml_tree(self, tree, source_encoding, target_encoding):
        pipeline = self.build_pipeline(source_encoding, target_encoding)

        converted_paragraphs = 0
        converted_chars = 0

        for para in tree.findall(".//w:p", NS):
            p_count, c_count = self.convert_paragraph(
                para,
                source_encoding=source_encoding,
                target_encoding=target_encoding,
                pipeline=pipeline
            )
            converted_paragraphs += p_count
            converted_chars += c_count

        return converted_paragraphs, converted_chars

    def convert_docx(self, file_storage, source_encoding, target_encoding):
        self.refresh()
        pipeline = self.build_pipeline(source_encoding, target_encoding)

        temp_root = tempfile.mkdtemp(prefix="tamil_docx_")
        input_name = Path(file_storage.filename or "document.docx").name
        src_tag = safe_filename_part(source_encoding)
        dst_tag = safe_filename_part(target_encoding)
        output_name = f"{Path(input_name).stem}_{src_tag}_to_{dst_tag}.docx"
        input_bytes = file_storage.read()

        try:
            with zipfile.ZipFile(io.BytesIO(input_bytes), "r") as zf:
                zf.extractall(temp_root)

            self.parse_theme_fonts(temp_root)
            self.parse_settings_theme_lang(temp_root)
            self.parse_styles(temp_root)

            total_paragraphs = 0
            total_chars = 0

            for xml_path in self.story_parts(temp_root):
                try:
                    tree = ET.parse(xml_path)
                except ET.ParseError:
                    continue

                paragraphs, chars = self.convert_xml_tree(tree, source_encoding, target_encoding)
                if paragraphs or chars:
                    tree.write(xml_path, encoding="utf-8", xml_declaration=True)

                total_paragraphs += paragraphs
                total_chars += chars

            out_path = OUTPUT_DIR / output_name
            with zipfile.ZipFile(out_path, "w", zipfile.ZIP_DEFLATED) as zf:
                for folder, _, files in os.walk(temp_root):
                    for fname in files:
                        full = Path(folder) / fname
                        zf.write(full, full.relative_to(temp_root).as_posix())

            return out_path, total_paragraphs, total_chars, pipeline

        finally:
            shutil.rmtree(temp_root, ignore_errors=True)


converter = TamilDocxConverter()


@app.errorhandler(RequestEntityTooLarge)
def handle_large_file(_e):
    return jsonify({
        "ok": False,
        "error": "File too large. Maximum allowed size is 100 MB."
    }), 413


@app.get("/")
def home():
    converter.refresh()
    fonts = converter.known_encodings()

    pairs = sorted(
        [
            {
                "source": s,
                "target": t,
                "count": len(v["map"]),
                "file": v["file"],
                "kind": v["kind"],
                "source_doc_font": converter.doc_font_for_encoding(s),
                "target_doc_font": converter.doc_font_for_encoding(t)
            }
            for (s, t), v in converter.mappings.items()
            if s != t
        ],
        key=lambda x: (x["source"], x["target"])
    )

    encodings = [
        {
            "name": e,
            "doc_font": converter.doc_font_for_encoding(e),
            "aliases": sorted(converter.doc_font_aliases(e))
        }
        for e in fonts
    ]

    return render_template(
        "index.html",
        fonts=fonts,
        encodings=encodings,
        pairs=pairs,
        mapping_count=len(pairs),
        font_config=converter.font_config,
        mapping_errors=converter.mapping_errors
    )


@app.get("/api/debug/mappings")
def debug_mappings():
    converter.refresh()
    return jsonify({
        "ok": True,
        "base_unicode_maps": [
            {
                "encoding": k,
                "file": v["file"],
                "count": len(v["map"])
            }
            for k, v in sorted(converter.base_unicode_maps.items())
        ],
        "known_encodings": converter.known_encodings(),
        "pair_count": len([1 for (s, t) in converter.mappings.keys() if s != t]),
        "pairs": [
            {
                "source": s,
                "target": t,
                "file": v["file"],
                "kind": v["kind"],
                "count": len(v["map"])
            }
            for (s, t), v in sorted(converter.mappings.items())
            if s != t
        ],
        "errors": converter.mapping_errors
    })


@app.post("/api/convert")
def convert_api():
    file = request.files.get("docx")
    source_font = (request.form.get("source_font") or "").strip().lower()
    target_font = (request.form.get("target_font") or "").strip().lower()

    if not file or not file.filename.lower().endswith(".docx"):
        return jsonify({"ok": False, "error": "Choose a valid .docx file"}), 400
    if not source_font or not target_font:
        return jsonify({"ok": False, "error": "Choose source and target fonts"}), 400
    if source_font == target_font:
        return jsonify({"ok": False, "error": "Source and target must be different"}), 400

    try:
        out_path, paragraphs, chars, pipeline = converter.convert_docx(file, source_font, target_font)

        return jsonify({
            "ok": True,
            "filename": out_path.name,
            "paragraphs": paragraphs,
            "chars": chars,
            "download": f"/download/{out_path.name}",
            "pipeline": [
                {"source": s, "target": t, "file": m["file"], "kind": m["kind"]}
                for s, t, m in pipeline
            ],
            "source_doc_font": converter.doc_font_for_encoding(source_font),
            "target_doc_font": converter.doc_font_for_encoding(target_font)
        })
    except Exception as e:
        return jsonify({"ok": False, "error": str(e)}), 500


@app.get("/download/<filename>")
def download(filename):
    return send_file(OUTPUT_DIR / filename, as_attachment=True, download_name=filename)


def open_browser():
    webbrowser.open("http://127.0.0.1:5000")


if __name__ == "__main__":
    print("\nTamil DOCX Font Converter")
    print(f"Folder: {BASE_DIR}")
    print(f"Mappings: {MAPPINGS_DIR}")
    print("Open: http://127.0.0.1:5000")
    print("Mode: build mappings from *_to_unicode.js, convert legacy↔unicode and legacy↔legacy via Unicode pivot")
    print("Debug mappings: http://127.0.0.1:5000/api/debug/mappings\n")
    Timer(1.2, open_browser).start()
    app.run(host="0.0.0.0", port=5000, debug=False)
