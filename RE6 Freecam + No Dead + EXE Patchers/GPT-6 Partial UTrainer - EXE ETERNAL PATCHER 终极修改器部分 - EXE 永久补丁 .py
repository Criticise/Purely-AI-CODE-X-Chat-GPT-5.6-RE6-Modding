"""Signature-based BH6.exe patcher with a bilingual GUI and exact input backups."""

from __future__ import annotations

import argparse
import hashlib
import os
from pathlib import Path
import queue
import re
import struct
import subprocess
import sys
import threading
import time
from collections import deque
from dataclasses import dataclass


TITLE = "GPT-6 Partial UTrainer - EXE ETERNAL PATCHER"
CHINESE_TITLE = "GPT-6 终极修改器部分功能 - EXE永久补丁"
OUTPUT_FOLDER = "输出 OUTPUT"


class PatchError(ValueError):
    pass


class PendingPatchError(PatchError):
    pass


@dataclass(frozen=True)
class Section:
    name: str
    virtual_address: int
    virtual_size: int
    raw_offset: int
    raw_size: int
    characteristics: int


class PEImage:
    def __init__(self, data: bytes):
        self.data = data
        if len(data) < 0x40 or data[:2] != b"MZ":
            raise PatchError("The selected file is not a DOS/PE executable.")
        self.pe_offset = struct.unpack_from("<I", data, 0x3C)[0]
        if self.pe_offset + 24 > len(data):
            raise PatchError("The PE header is truncated.")
        if data[self.pe_offset:self.pe_offset + 4] != b"PE\0\0":
            raise PatchError("The PE signature is invalid.")
        machine, count, _, _, _, optional_size, characteristics = struct.unpack_from(
            "<HHIIIHH", data, self.pe_offset + 4
        )
        if machine != 0x14C or not characteristics & 0x0002:
            raise PatchError("Only x86 PE executables are supported.")
        if not 1 <= count <= 96 or optional_size < 96:
            raise PatchError("The PE section count or optional header is invalid.")
        self.optional_offset = self.pe_offset + 24
        section_offset = self.optional_offset + optional_size
        if section_offset + count * 40 > len(data):
            raise PatchError("The PE section table is truncated.")
        if struct.unpack_from("<H", data, self.optional_offset)[0] != 0x10B:
            raise PatchError("Only PE32 executables are supported.")
        self.image_base = struct.unpack_from("<I", data, self.optional_offset + 28)[0]
        self.section_alignment, self.file_alignment = struct.unpack_from(
            "<II", data, self.optional_offset + 32
        )
        self.size_of_image, self.size_of_headers = struct.unpack_from(
            "<II", data, self.optional_offset + 56
        )
        if not self.section_alignment or not self.file_alignment:
            raise PatchError("The PE alignment is invalid.")
        if not section_offset + count * 40 <= self.size_of_headers <= len(data):
            raise PatchError("The PE header size is invalid.")
        sections = []
        for index in range(count):
            offset = section_offset + index * 40
            fields = struct.unpack_from("<8sIIIIIIHHI", data, offset)
            name = fields[0].rstrip(b"\0").decode("ascii", errors="replace")
            virtual_size, virtual_address, raw_size, raw_offset = fields[1:5]
            if raw_size and (raw_offset < self.size_of_headers or raw_offset + raw_size > len(data)):
                raise PatchError(f"The {name} section has invalid file bounds.")
            if virtual_address + max(virtual_size, raw_size) > self.size_of_image:
                raise PatchError(f"The {name} section exceeds the loaded image.")
            sections.append(Section(name, virtual_address, virtual_size, raw_offset, raw_size, fields[-1]))
        self.sections = tuple(sections)

    def rva_to_offset(self, rva: int, size: int = 1) -> int:
        if rva < 0 or size <= 0 or rva + size > 0x100000000:
            raise PatchError("Invalid RVA or patch length.")
        if rva < self.size_of_headers:
            if rva + size <= self.size_of_headers:
                return rva
            raise PatchError("The patch crosses the PE header boundary.")
        matches = [s for s in self.sections if s.virtual_address <= rva < s.virtual_address + max(s.virtual_size, s.raw_size)]
        if len(matches) != 1:
            raise PatchError(f"RVA 0x{rva:X} does not map to one PE section.")
        section = matches[0]
        delta = rva - section.virtual_address
        if delta + size > section.raw_size:
            raise PatchError(f"RVA 0x{rva:X} is not fully backed by file bytes.")
        return section.raw_offset + delta


@dataclass(frozen=True)
class BytePatch:
    rva: int
    original: bytes
    replacement: bytes


@dataclass(frozen=True)
class Feature:
    name: str
    edits: tuple[BytePatch, ...]
    ready: bool = True
    runtime_only: bool = False
    differences: int = 0


MISSING_SIGNATURE = (
    "?? ?? ?? ?? 81 EC ?? ?? ?? ?? 8D 84 24 ?? ?? ?? ?? 50 51 6A FF "
    "8D 54 24 ?? 68 ?? ?? ?? ?? 52 E8 ?? ?? ?? ?? 8B 8C 24 ?? ?? ?? ?? "
    "8B 41 0C 83 C4 14 85 C0 74 ?? 8B 49 20 51 8D 54 24 ?? 52 FF D0 "
    "83 C4 08 6A 01 E8 ?? ?? ?? ??"
)
RENDER_SIGNATURE = (
    "F7 87 ?? ?? ?? ?? 00 00 00 80 ?? ?? ?? ?? ?? ?? ?? ?? "
    "80 B9 ?? ?? ?? ?? 00 75 ?? 33 DB C6 44 24 ?? 01 EB ?? "
    "A8 08 74 ?? BB 02 00 00 00 EB ?? A9 00 02 00 00 74 ?? "
    "BB 04 00 00 00 EB ??"
)


def find_signature(image: PEImage, name: str, signature: str, valid_site, tolerance: int = 3) -> tuple[int, int]:
    """Find the unique best code match, ignoring operands and up to three changed bytes."""
    pattern = tuple(None if token == "??" else int(token, 16) for token in signature.split())
    fixed = [(index, value) for index, value in enumerate(pattern) if value is not None]
    # Split fixed bytes into four disjoint seeds. With at most three changed
    # bytes, at least one seed still matches exactly, including distant RVAs.
    seeds = []
    for group in range(tolerance + 1):
        part = fixed[group * len(fixed) // (tolerance + 1):(group + 1) * len(fixed) // (tolerance + 1)]
        if not part:
            raise PatchError("The signature is too short for this tolerance.")
        start, end = part[0][0], part[-1][0] + 1
        expression = b"".join(b"." if value is None else re.escape(bytes([value])) for value in pattern[start:end])
        seeds.append((start, re.compile(expression, re.DOTALL)))
    matches = {}
    for section in image.sections:
        if not section.characteristics & 0x20000000 or not section.raw_size:
            continue
        code = image.data[section.raw_offset:section.raw_offset + section.raw_size]
        candidates = set()
        for relative, seed in seeds:
            for match in seed.finditer(code):
                position = match.start() - relative
                if 0 <= position <= len(code) - len(pattern):
                    candidates.add(position)
        for position in candidates:
            window = code[position:position + len(pattern)]
            differences = sum(window[index] != value for index, value in fixed)
            if differences <= tolerance and valid_site(window):
                matches[section.virtual_address + position] = differences
    if not matches:
        raise PatchError(f"{name}: no matching instruction sequence found (up to {tolerance} changed fixed bytes allowed).")
    best_score = min(matches.values())
    best = [rva for rva, score in matches.items() if score == best_score]
    if len(best) != 1:
        locations = ", ".join(f"0x{rva:X}" for rva in sorted(best))
        raise PatchError(f"{name}: equally matching locations: {locations}")
    return best[0], best_score


def feature_definitions(image: PEImage) -> tuple[Feature, ...]:
    missing_replacement = bytes.fromhex("C3 90 90 90")
    def missing_site(window: bytes) -> bool:
        return window[:4] == missing_replacement or (window[0] == 0x8B and window[1] & 0xC7 == 0x44 and window[2] == 0x24)
    def render_site(window: bytes) -> bool:
        # Only replace a two-byte branch opcode; keep its actual displacement.
        return (0x70 <= window[10] <= 0x7F or window[10] == 0xEB) and 0 < window[11] < 0x80
    missing_rva, missing_differences = find_signature(image, "Missing Files Fix", MISSING_SIGNATURE, missing_site)
    render_rva, render_differences = find_signature(image, "Render Everything", RENDER_SIGNATURE, render_site)
    render_rva += 10
    missing_offset = image.rva_to_offset(missing_rva, 4)
    render_offset = image.rva_to_offset(render_rva)
    return (
        Feature("Missing Files Fix", (BytePatch(missing_rva, image.data[missing_offset:missing_offset + 4], missing_replacement),), differences=missing_differences),
        Feature("Render Everything", (BytePatch(render_rva, image.data[render_offset:render_offset + 1], b"\xEB"),), differences=render_differences),
        # UNFINISHED: neither a full CT implementation nor an EXE patch is available.
        Feature("Auto-Fix Textures [UNFINISHED]", (), ready=False, runtime_only=True),
    )


def validate_original(data: bytes) -> PEImage:
    return PEImage(data)


def inspect_original(data: bytes) -> tuple[PEImage, tuple[Feature, ...]]:
    image = validate_original(data)
    features = feature_definitions(image)
    occupied: set[int] = set()
    for feature in features:
        if feature.runtime_only or not feature.ready:
            continue
        if not feature.edits:
            raise PatchError(f"{feature.name}: the patch has no byte edits.")
        for edit in feature.edits:
            if not edit.original or len(edit.original) != len(edit.replacement):
                raise PatchError(f"{feature.name}: invalid replacement length.")
            offset = image.rva_to_offset(edit.rva, len(edit.original))
            if data[offset:offset + len(edit.original)] != edit.original:
                raise PatchError(f"{feature.name}: original bytes do not match at RVA 0x{edit.rva:X}.")
            addresses = set(range(offset, offset + len(edit.original)))
            if addresses & occupied:
                raise PatchError(f"{feature.name}: patch ranges overlap.")
            occupied.update(addresses)
    return image, features


def build_patched(data: bytes) -> bytes:
    image, features = inspect_original(data)
    pending = [feature.name for feature in features if not feature.ready and not feature.runtime_only]
    if pending:
        raise PendingPatchError("Patch definitions are not complete: " + ", ".join(pending))
    result = bytearray(data)
    for feature in features:
        for edit in feature.edits:
            offset = image.rva_to_offset(edit.rva, len(edit.original))
            result[offset:offset + len(edit.replacement)] = edit.replacement
    return bytes(result)


@dataclass(frozen=True)
class PatchResult:
    executable: Path
    backup: Path
    original_sha256: str
    patched_sha256: str
    created_executable: bool
    created_backup: bool


def _check_output(path: Path, content: bytes, source: Path) -> None:
    if path.resolve() == source.resolve():
        raise PatchError(f"The output cannot replace the source file: {path}")
    if path.exists():
        if os.path.samefile(path, source):
            raise PatchError(f"The output is another link to the source file: {path}")
        if not path.is_file() or path.read_bytes() != content:
            raise PatchError(f"An existing output differs; choose an empty output folder:\n{path}")


def _write_new_or_identical(path: Path, content: bytes) -> bool:
    try:
        handle = path.open("xb")
    except FileExistsError:
        if path.is_file() and path.read_bytes() == content:
            return False
        raise PatchError(f"An existing output differs and was left unchanged:\n{path}") from None
    try:
        with handle:
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
    except BaseException:
        path.unlink(missing_ok=True)
        raise
    return True


def generate_files(source: Path, output_directory: Path) -> PatchResult:
    source = Path(source).expanduser().resolve(strict=True)
    if not source.is_file():
        raise PatchError("Select an original BH6.exe file.")
    original = source.read_bytes()
    patched = build_patched(original)
    output_directory = Path(output_directory).expanduser().resolve()
    executable = output_directory / "BH6.exe"
    backup = output_directory / "BAK" / "BH6.original.exe"
    for path, content in ((executable, patched), (backup, original)):
        _check_output(path, content, source)
    backup.parent.mkdir(parents=True, exist_ok=True)
    created_backup = _write_new_or_identical(backup, original)
    created_executable = _write_new_or_identical(executable, patched)
    if backup.read_bytes() != original or executable.read_bytes() != patched:
        raise PatchError("Output verification failed; the source file was not changed.")
    return PatchResult(executable, backup, hashlib.sha256(original).hexdigest(), hashlib.sha256(patched).hexdigest(), created_executable, created_backup)


def game_executable_in(directory: Path) -> Path | None:
    """Identify a game installation by its nativePC directory and exact EXE name."""
    try:
        with os.scandir(directory) as entries:
            children = list(entries)
        if not any(entry.name.casefold() == "nativepc" and entry.is_dir() for entry in children):
            return None
        for entry in children:
            if entry.name.casefold() == "bh6.exe" and entry.is_file():
                return Path(entry.path).resolve()
    except OSError:
        return None
    return None


def find_game_executable(search_from: Path | None = None) -> Path | None:
    """Prefer the enclosing installation, then search nearby and common game folders."""
    start = Path(search_from or __file__).resolve()
    anchors = [start if start.is_dir() else start.parent, Path.cwd().resolve()]
    checked: set[str] = set()
    for anchor in anchors:
        for directory in (anchor, *anchor.parents):
            key = str(directory).casefold()
            if key in checked:
                continue
            checked.add(key)
            executable = game_executable_in(directory)
            if executable:
                return executable

    home = Path.home()
    roots = anchors + [home / "Desktop", home / "Downloads", home / "Games"]
    for variable in ("PROGRAMFILES(X86)", "PROGRAMFILES"):
        if os.environ.get(variable):
            roots.append(Path(os.environ[variable]) / "Steam" / "steamapps" / "common")
    if os.name == "nt":
        for letter in "CDEFGHIJKLMNOPQRSTUVWXYZ":
            drive = Path(f"{letter}:/")
            if drive.exists():
                roots.extend(drive / name for name in ("Games", "SteamLibrary/steamapps/common", "Steam/steamapps/common"))
    pending = deque((root, 0) for root in roots)
    visited: set[str] = set()
    deadline = time.monotonic() + 15
    ignored = {"nativepc", "nativepc_dlc", "bak", OUTPUT_FOLDER.casefold(), "node_modules", ".git", "$recycle.bin", "system volume information"}
    # Bound the background scan so unavailable disks or large mod trees cannot hold the UI open indefinitely.
    while pending and len(visited) < 12000 and time.monotonic() < deadline:
        directory, depth = pending.popleft()
        key = str(directory).casefold()
        if key in visited:
            continue
        visited.add(key)
        executable = game_executable_in(directory)
        if executable:
            return executable
        if depth >= 5:
            continue
        try:
            with os.scandir(directory) as entries:
                children = sorted((Path(entry.path) for entry in entries if entry.name.casefold() not in ignored and entry.is_dir(follow_symlinks=False)), key=lambda path: path.name.casefold())
            pending.extend((child, depth + 1) for child in children)
        except OSError:
            continue
    return None


def launch_gui(input_path: str | None = None, output_dir: str | None = None) -> None:
    import tkinter as tk
    from tkinter import filedialog, messagebox, ttk

    class PatcherWindow:
        def __init__(self, root: tk.Tk):
            self.root = root
            self.events: queue.Queue = queue.Queue()
            self.busy = False
            self.validated_source: str | None = None
            self.language = tk.StringVar(value="zh")
            self.theme = "dark"
            self.status_key = "select"
            self.feature_states = ["waiting", "waiting", "runtime"]
            self.messages = {
                "zh": {
                    "source": "原版 EXE", "destination": "输出目录", "browse_file": "选择文件...", "browse_folder": "选择目录...",
                    "scan": "自动查找游戏", "check": "验证文件", "generate": "生成 EXE 和原版备份", "patch": "补丁", "state": "状态",
                    "select": "请选择 BH6.exe", "waiting": "等待扫描", "checking": "正在扫描指令特征码...",
                    "scanning": "正在查找包含 nativePC 和 BH6.exe 的游戏目录...", "not_found": "未找到游戏目录，请手动选择游戏目录中的 BH6.exe。",
                    "select_output": "请选择输出目录", "generating": "正在生成和校验文件...", "error": "操作未完成，请查看下方详情",
                    "verified": "特征码已定位", "runtime": "未完成，不写入 EXE", "pending": "补丁定义待完成", "ready": "两项特征码已定位，可以生成 EXE 和输入备份",
                    "textures_name": "Auto-Fix Textures [未完成]",
                    "incomplete": "原版验证通过；补丁定义未齐全，暂不可生成", "complete": "生成完成", "existing": "输出已经是当前补丁版本",
                    "choose_source": "选择原版 BH6.exe", "choose_destination": "选择输出目录", "busy": "文件操作仍在进行，请等待完成。",
                    "invalid_source": "请选择游戏目录中的 BH6.exe；同一目录必须包含 nativePC 文件夹。", "original": "原版", "new_exe": "新 EXE", "backup": "原版备份",
                    "dark": "深色", "light": "浅色",
                },
                "en": {
                    "source": "Original EXE", "destination": "Output folder", "browse_file": "Browse file...", "browse_folder": "Browse folder...",
                    "scan": "Find game", "check": "Validate file", "generate": "Create EXE and backup", "patch": "Patch", "state": "Status",
                    "select": "Select BH6.exe", "waiting": "Awaiting scan", "checking": "Scanning instruction signatures...",
                    "scanning": "Finding a game directory containing nativePC and BH6.exe...", "not_found": "No game directory found. Select BH6.exe from your game directory.",
                    "select_output": "Choose an output folder", "generating": "Creating and verifying files...", "error": "Operation failed; see the details below",
                    "verified": "Signature located", "runtime": "Unfinished; not in EXE", "pending": "Patch definition pending", "ready": "Both signatures located, ready to create EXE and input backup",
                    "textures_name": "Auto-Fix Textures [UNFINISHED]",
                    "incomplete": "Original verified; patch definitions are incomplete", "complete": "Files created", "existing": "Output is already the current patched version",
                    "choose_source": "Select original BH6.exe", "choose_destination": "Choose output folder", "busy": "A file operation is still running. Please wait.",
                    "invalid_source": "Select BH6.exe from the game directory; nativePC must be a sibling folder.", "original": "Original", "new_exe": "New EXE", "backup": "Original backup",
                    "dark": "Dark", "light": "Light",
                },
            }
            self.source = tk.StringVar(value=input_path or "")
            self.destination = tk.StringVar(value=output_dir or "")
            self.status = tk.StringVar()
            root.geometry("940x620")
            root.minsize(820, 540)
            root.option_add("*Font", ("Microsoft YaHei", 10))
            self.style = ttk.Style(root)
            self.style.theme_use("clam")
            frame = ttk.Frame(root, padding=18)
            frame.grid(sticky="nsew")
            root.columnconfigure(0, weight=1)
            root.rowconfigure(0, weight=1)
            frame.columnconfigure(1, weight=1)
            frame.rowconfigure(6, weight=1)
            languages = ttk.Frame(frame)
            languages.grid(row=0, column=0, columnspan=3, sticky="e", pady=(0, 12))
            self.dark_button = ttk.Button(languages, width=8, command=lambda: self.apply_theme("dark"))
            self.dark_button.pack(side="left", padx=(0, 6))
            self.light_button = ttk.Button(languages, width=8, command=lambda: self.apply_theme("light"))
            self.light_button.pack(side="left", padx=(0, 20))
            self.chinese_button = ttk.Button(languages, text="中文", width=8, command=lambda: self.change_language("zh"))
            self.chinese_button.pack(side="left", padx=(0, 6))
            self.english_button = ttk.Button(languages, text="English", width=8, command=lambda: self.change_language("en"))
            self.english_button.pack(side="left")

            self.source_label = ttk.Label(frame)
            self.source_label.grid(row=1, column=0, sticky="w", padx=(0, 10), pady=5)
            self.source_entry = ttk.Entry(frame, textvariable=self.source)
            self.source_entry.grid(row=1, column=1, sticky="ew", pady=5)
            self.source_button = ttk.Button(frame, command=self.choose_source, width=16)
            self.source_button.grid(row=1, column=2, padx=(8, 0))
            self.destination_label = ttk.Label(frame)
            self.destination_label.grid(row=2, column=0, sticky="w", padx=(0, 10), pady=5)
            self.destination_entry = ttk.Entry(frame, textvariable=self.destination)
            self.destination_entry.grid(row=2, column=1, sticky="ew", pady=5)
            self.destination_button = ttk.Button(frame, command=self.choose_destination, width=16)
            self.destination_button.grid(row=2, column=2, padx=(8, 0))

            self.features = ttk.Treeview(frame, columns=("state",), show="tree headings", height=3, selectmode="none")
            self.features.column("#0", width=330, minwidth=220)
            self.features.column("state", width=180, minwidth=120)
            self.features.grid(row=3, column=0, columnspan=3, sticky="ew", pady=(14, 10))
            for index, name in enumerate(("Missing Files Fix", "Render Everything", "Auto-Fix Textures")):
                self.features.insert("", "end", iid=str(index), text=name)
            self.status_label = ttk.Label(frame, textvariable=self.status, wraplength=770)
            self.status_label.grid(row=4, column=0, columnspan=3, sticky="ew", pady=(0, 12))
            self.status_label.bind("<Configure>", lambda event: self.status_label.configure(wraplength=max(100, event.width)))
            actions = ttk.Frame(frame)
            actions.grid(row=5, column=0, columnspan=3, sticky="ew", pady=(0, 12))
            self.scan_button = ttk.Button(actions, command=self.scan_source)
            self.scan_button.pack(side="left", padx=(0, 8))
            self.check_button = ttk.Button(actions, command=self.check_source)
            self.check_button.pack(side="left")
            self.generate_button = ttk.Button(actions, command=self.generate, state="disabled", style="Primary.TButton")
            self.generate_button.pack(side="right")
            log_frame = ttk.Frame(frame)
            log_frame.grid(row=6, column=0, columnspan=3, sticky="nsew")
            log_frame.columnconfigure(0, weight=1)
            log_frame.rowconfigure(0, weight=1)
            self.log = tk.Text(log_frame, height=10, wrap="word", state="disabled", font=("Microsoft YaHei", 10), background="#161719", foreground="#d7dbdf", insertbackground="#ffffff", selectbackground="#376a80", relief="flat", padx=10, pady=8)
            self.log.grid(row=0, column=0, sticky="nsew")
            scrollbar = ttk.Scrollbar(log_frame, orient="vertical", command=self.log.yview)
            scrollbar.grid(row=0, column=1, sticky="ns")
            self.log.configure(yscrollcommand=scrollbar.set)
            self.source.trace_add("write", self.invalidate)
            root.bind("<Map>", lambda event: root.after_idle(self.apply_titlebar_theme) if event.widget == root else None, add="+")
            self.apply_theme("dark")
            self.change_language("zh")
            root.after(100, self.poll)
            root.protocol("WM_DELETE_WINDOW", self.close)
            if input_path:
                if not output_dir:
                    self.destination.set(str(Path(input_path).parent / OUTPUT_FOLDER))
                root.after(100, self.check_source)
            else:
                root.after(150, self.scan_source)

        def text(self, key: str) -> str:
            return self.messages[self.language.get()][key]

        def set_status(self, key: str) -> None:
            self.status_key = key
            self.status.set(self.text(key))

        def change_language(self, language: str) -> None:
            self.language.set(language)
            self.root.title(CHINESE_TITLE if language == "zh" else TITLE)
            for widget, key in ((self.source_label, "source"), (self.destination_label, "destination"), (self.source_button, "browse_file"), (self.destination_button, "browse_folder"), (self.scan_button, "scan"), (self.check_button, "check"), (self.generate_button, "generate"), (self.dark_button, "dark"), (self.light_button, "light")):
                widget.configure(text=self.text(key))
            self.features.heading("#0", text=self.text("patch"))
            self.features.heading("state", text=self.text("state"))
            self.features.item("2", text=self.text("textures_name"))
            for index, state in enumerate(self.feature_states):
                self.features.set(str(index), "state", self.text(state))
            self.set_status(self.status_key)
            self.chinese_button.configure(style="Selected.TButton" if language == "zh" else "TButton")
            self.english_button.configure(style="Selected.TButton" if language == "en" else "TButton")

        def apply_theme(self, theme: str) -> None:
            self.theme = theme
            if theme == "dark":
                colors = dict(bg="#202124", fg="#eeeeee", field="#303236", panel="#292b2e", button="#393b3f", hover="#505359", pressed="#202124", border="#55585c", disabled="#2b2c2f", muted="#85888b", selected="#555a60", selected_border="#a2a8ae", log="#161719", accent="#285c72", accent_hover="#34728c", accent_pressed="#204958")
            else:
                colors = dict(bg="#f2f3f5", fg="#22252a", field="#ffffff", panel="#ffffff", button="#e1e4e8", hover="#d2d8df", pressed="#c6cdd5", border="#aeb7c1", disabled="#e5e7eb", muted="#7a828c", selected="#c3d8e3", selected_border="#547b91", log="#ffffff", accent="#276783", accent_hover="#347c9d", accent_pressed="#1c4f67")
            style = self.style
            self.root.configure(background=colors["bg"])
            style.configure(".", font=("Microsoft YaHei", 10), background=colors["bg"], foreground=colors["fg"])
            style.configure("TFrame", background=colors["bg"])
            style.configure("TLabel", background=colors["bg"], foreground=colors["fg"])
            style.configure("TButton", background=colors["button"], foreground=colors["fg"], padding=(14, 8), borderwidth=1, bordercolor=colors["border"], focusthickness=1, focuscolor=colors["selected_border"])
            style.map("TButton", background=[("disabled", colors["disabled"]), ("pressed", colors["pressed"]), ("active", colors["hover"])], foreground=[("disabled", colors["muted"])])
            style.configure("Primary.TButton", background=colors["accent"], foreground="#ffffff", bordercolor=colors["selected_border"])
            style.map("Primary.TButton", background=[("disabled", colors["disabled"]), ("pressed", colors["accent_pressed"]), ("active", colors["accent_hover"])], foreground=[("disabled", colors["muted"]), ("!disabled", "#ffffff")])
            style.configure("Selected.TButton", background=colors["selected"], bordercolor=colors["selected_border"])
            style.map("Selected.TButton", background=[("pressed", colors["pressed"]), ("active", colors["selected"])])
            style.configure("TEntry", fieldbackground=colors["field"], foreground=colors["fg"], insertcolor=colors["fg"], padding=7, bordercolor=colors["border"])
            style.map("TEntry", fieldbackground=[("disabled", colors["disabled"])], foreground=[("disabled", colors["muted"])])
            style.configure("Treeview", fieldbackground=colors["panel"], background=colors["panel"], foreground=colors["fg"], rowheight=35, bordercolor=colors["border"])
            style.configure("Treeview.Heading", background=colors["button"], foreground=colors["fg"], padding=(8, 7), font=("Microsoft YaHei", 10))
            style.map("Treeview.Heading", background=[("active", colors["hover"])])
            style.configure("Vertical.TScrollbar", background=colors["button"], troughcolor=colors["log"], bordercolor=colors["border"], arrowcolor=colors["fg"])
            style.map("Vertical.TScrollbar", background=[("active", colors["hover"]), ("pressed", colors["pressed"])])
            self.log.configure(background=colors["log"], foreground=colors["fg"], insertbackground=colors["fg"], selectbackground=colors["accent"], selectforeground="#ffffff")
            self.dark_button.configure(style="Selected.TButton" if theme == "dark" else "TButton")
            self.light_button.configure(style="Selected.TButton" if theme == "light" else "TButton")
            self.root.after_idle(self.apply_titlebar_theme)

        def apply_titlebar_theme(self) -> None:
            if os.name != "nt":
                return
            import ctypes
            from ctypes import wintypes

            user32 = ctypes.WinDLL("user32", use_last_error=True)
            dwmapi = ctypes.WinDLL("dwmapi")
            user32.GetAncestor.argtypes = (wintypes.HWND, wintypes.UINT)
            user32.GetAncestor.restype = wintypes.HWND
            dwmapi.DwmSetWindowAttribute.argtypes = (wintypes.HWND, wintypes.DWORD, ctypes.c_void_p, wintypes.DWORD)
            dwmapi.DwmSetWindowAttribute.restype = ctypes.c_long
            # Tk's widget HWND is a child; Windows draws the caption on its wrapper.
            handle = user32.GetAncestor(self.root.winfo_id(), 2)
            if not handle:
                return
            dark = wintypes.BOOL(self.theme == "dark")
            result = dwmapi.DwmSetWindowAttribute(handle, 20, ctypes.byref(dark), ctypes.sizeof(dark))
            if result != 0:
                dwmapi.DwmSetWindowAttribute(handle, 19, ctypes.byref(dark), ctypes.sizeof(dark))
            # Explicit Windows 11 caption/text colors also cover inactive windows.
            caption = wintypes.DWORD(0x00242120 if dark.value else 0x00F5F3F2)
            text = wintypes.DWORD(0x00EEEEEE if dark.value else 0x002A2522)
            dwmapi.DwmSetWindowAttribute(handle, 35, ctypes.byref(caption), ctypes.sizeof(caption))
            dwmapi.DwmSetWindowAttribute(handle, 36, ctypes.byref(text), ctypes.sizeof(text))
            user32.SetWindowPos.argtypes = (wintypes.HWND, wintypes.HWND, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int, wintypes.UINT)
            user32.SetWindowPos.restype = wintypes.BOOL
            user32.SetWindowPos(handle, None, 0, 0, 0, 0, 0x0037)

        def append_log(self, message: str) -> None:
            self.log.configure(state="normal")
            self.log.insert("end", message + "\n")
            self.log.see("end")
            self.log.configure(state="disabled")

        def invalidate(self, *_: object) -> None:
            self.validated_source = None
            self.generate_button.configure(state="disabled")
            self.set_status("waiting")
            self.feature_states = ["waiting", "waiting", "runtime"]
            for index, state in enumerate(self.feature_states):
                self.features.set(str(index), "state", self.text(state))
            if not output_dir and self.source.get().strip():
                self.destination.set(str(Path(self.source.get().strip()).parent / OUTPUT_FOLDER))

        def scan_source(self) -> None:
            if self.busy:
                return
            self.set_status("scanning")
            self.work("scan", find_game_executable)

        def choose_source(self) -> None:
            name = filedialog.askopenfilename(title=self.text("choose_source"), initialdir=str(Path(self.source.get()).parent) if self.source.get() else None, filetypes=(("BH6.exe", "BH6.exe"), ("Executables", "*.exe")))
            if name:
                self.source.set(name)
                self.check_source()

        def choose_destination(self) -> None:
            name = filedialog.askdirectory(title=self.text("choose_destination"), initialdir=self.destination.get() or None, mustexist=False)
            if name:
                self.destination.set(name)

        def set_busy(self, busy: bool) -> None:
            self.busy = busy
            state = "disabled" if busy else "normal"
            for widget in (self.source_entry, self.destination_entry, self.source_button, self.destination_button, self.scan_button, self.check_button):
                widget.configure(state=state)
            self.generate_button.configure(state="normal" if not busy and self.validated_source else "disabled")

        def work(self, operation: str, callback) -> None:
            self.set_busy(True)
            def run():
                try:
                    self.events.put((operation, callback(), None))
                except Exception as exc:
                    self.events.put((operation, None, str(exc)))
            threading.Thread(target=run, daemon=False).start()

        def check_source(self) -> None:
            if self.busy:
                return
            path = self.source.get().strip()
            if not path:
                return
            self.validated_source = None
            self.set_status("checking")
            invalid_source = self.text("invalid_source")
            def check():
                source = Path(path).expanduser().resolve()
                discovered = game_executable_in(source.parent)
                if source.name.casefold() != "bh6.exe" or discovered is None or discovered != source:
                    raise PatchError(invalid_source)
                data = source.read_bytes()
                return path, inspect_original(data)[1], hashlib.sha256(data).hexdigest()
            self.work("check", check)

        def generate(self) -> None:
            source = self.source.get().strip()
            destination = self.destination.get().strip()
            if not destination:
                self.set_status("select_output")
                return
            self.set_status("generating")
            self.work("generate", lambda: generate_files(Path(source), Path(destination)))

        def poll(self) -> None:
            try:
                operation, result, error = self.events.get_nowait()
            except queue.Empty:
                self.root.after(100, self.poll)
                return
            if error:
                self.set_status("error")
                self.append_log(error)
            elif operation == "scan":
                if result:
                    self.source.set(str(result))
                    self.set_busy(False)
                    self.check_source()
                    self.root.after(100, self.poll)
                    return
                self.set_status("not_found")
            elif operation == "check":
                path, features, source_digest = result
                complete = all(feature.ready or feature.runtime_only for feature in features)
                for index, feature in enumerate(features):
                    state = "runtime" if feature.runtime_only else ("verified" if feature.ready else "pending")
                    self.feature_states[index] = state
                    self.features.set(str(index), "state", self.text(state))
                if complete:
                    self.validated_source = path
                self.set_status("ready" if complete else "incomplete")
                self.append_log(f"{self.text('original')}: {path}\nSHA-256: {source_digest}")
                for feature in features:
                    for edit in feature.edits:
                        self.append_log(f"{feature.name}: RVA 0x{edit.rva:X}, {edit.original.hex(' ').upper()} -> {edit.replacement.hex(' ').upper()} ({feature.differences} {'处特征字节差异' if self.language.get() == 'zh' else 'signature byte differences'})")
            else:
                self.set_status("complete" if result.created_executable else "existing")
                self.append_log(f"{self.text('new_exe')}: {result.executable}\n{self.text('backup')}: {result.backup}\nSHA-256: {result.patched_sha256}")
            self.set_busy(False)
            self.root.after(100, self.poll)

        def close(self) -> None:
            if self.busy:
                messagebox.showinfo(self.root.title(), self.text("busy"))
                return
            self.root.destroy()

    root = tk.Tk()
    PatcherWindow(root)
    root.mainloop()


def start_gui_without_console(arguments: list[str]) -> bool:
    if os.name != "nt" or Path(sys.executable).name.casefold() == "pythonw.exe":
        return False
    interpreter = Path(sys.executable).with_name("pythonw.exe")
    if not interpreter.is_file():
        return False
    # Exit the console launcher after handing the GUI to the windowed interpreter.
    subprocess.Popen(
        [str(interpreter), str(Path(__file__).resolve()), *arguments],
        stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        creationflags=subprocess.CREATE_NO_WINDOW,
        close_fds=True,
    )
    return True


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=TITLE)
    parser.add_argument("--input", help="Original BH6.exe")
    parser.add_argument("--output-dir", help="Output folder (source file is never replaced)")
    parser.add_argument("--check", action="store_true", help="Validate without writing files")
    parser.add_argument("--cli", action="store_true", help="Generate without opening the GUI")
    args = parser.parse_args(argv)
    if args.check or args.cli:
        if not args.input:
            parser.error("--input is required for --check or --cli")
        try:
            source = Path(args.input)
            if args.check:
                patched = build_patched(source.read_bytes())
                print("Instruction signatures matched; no version or file-hash restriction.")
                print(f"Patched SHA-256: {hashlib.sha256(patched).hexdigest()}")
                return 0
            result = generate_files(source, Path(args.output_dir) if args.output_dir else source.parent / OUTPUT_FOLDER)
            print(f"Patched: {result.executable}")
            print(f"Backup: {result.backup}")
            print(f"Patched SHA-256: {result.patched_sha256}")
            return 0
        except (OSError, PatchError) as exc:
            print(str(exc), file=sys.stderr)
            return 1
    if start_gui_without_console(list(sys.argv[1:] if argv is None else argv)):
        return 0
    launch_gui(args.input, args.output_dir)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
