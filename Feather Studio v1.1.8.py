#!/usr/bin/env python3
"""
Feather Studio - Improved FL Studio-style DAW prototype
Python 3.13+
Requires: pip install pygame numpy
"""

import tkinter as tk
from tkinter import filedialog, messagebox, ttk
import pygame
import numpy as np
import os
import wave
import math
from pathlib import Path

# Initialize
pygame.mixer.init(frequency=44100, size=-16, channels=2, buffer=1024)
SAMPLE_RATE = 44100

NOTE_FREQS = {
    'C': 261.63, 'C#': 277.18, 'D': 293.66, 'D#': 311.13,
    'E': 329.63, 'F': 349.23, 'F#': 369.99, 'G': 392.00,
    'G#': 415.30, 'A': 440.00, 'A#': 466.16, 'B': 493.88
}

def generate_realistic_piano(frequency, duration=1.5, volume=0.4):
    """More realistic piano via additive synthesis + better envelope"""
    n_samples = int(SAMPLE_RATE * duration)
    t = np.linspace(0, duration, n_samples, False)
    # Multiple partials with decaying amplitudes
    wave = np.zeros(n_samples)
    for h in range(1, 8):
        amp = 1.0 / (h ** 1.2)
        wave += amp * np.sin(2 * np.pi * frequency * h * t)
    # Piano-like envelope (fast attack, slow decay)
    attack = int(0.01 * SAMPLE_RATE)
    decay = n_samples - attack
    env = np.ones(n_samples)
    env[:attack] = np.linspace(0, 1, attack)
    env[attack:] = np.exp(-2.5 * np.linspace(0, 1, decay))
    wave *= env * volume
    # Soft clipping
    wave = np.tanh(wave * 1.5) * 0.7
    stereo = np.column_stack((wave, wave * 0.98))  # slight stereo
    return (stereo * 32767).astype(np.int16)

def estimate_bpm(path, max_seconds=30):
    """Very simple BPM estimation from audio energy peaks. Returns float or None."""
    try:
        snd = pygame.mixer.Sound(path)
        arr = pygame.sndarray.array(snd)
        if arr.ndim == 2:
            mono = arr.mean(axis=1).astype(np.float32)
        else:
            mono = arr.astype(np.float32)
        mono = mono / (np.max(np.abs(mono)) + 1e-8)
        # Limit length
        max_samples = int(SAMPLE_RATE * max_seconds)
        mono = mono[:max_samples]
        # Simple energy envelope (downsampled)
        hop = 512
        energy = []
        for i in range(0, len(mono) - hop, hop):
            chunk = mono[i:i+hop]
            energy.append(np.sqrt(np.mean(chunk**2)))
        energy = np.array(energy)
        if len(energy) < 10:
            return None
        # Normalize
        energy = (energy - energy.mean()) / (energy.std() + 1e-8)
        # Autocorrelation
        corr = np.correlate(energy, energy, mode='full')
        corr = corr[len(corr)//2:]
        # Look for peaks in reasonable BPM range (60-200)
        min_lag = int(60 / 200 * SAMPLE_RATE / hop)  # ~60 BPM
        max_lag = int(60 / 60 * SAMPLE_RATE / hop)   # ~200 BPM
        min_lag = max(1, min_lag)
        max_lag = min(len(corr)-1, max_lag)
        if max_lag <= min_lag:
            return None
        peak_lag = min_lag + np.argmax(corr[min_lag:max_lag])
        if corr[peak_lag] < 0.2:  # weak correlation
            return None
        bpm = 60.0 * (SAMPLE_RATE / hop) / peak_lag
        # Clamp
        bpm = max(60, min(200, bpm))
        return round(bpm, 1)
    except Exception:
        return None

class MusicMaker:
    def __init__(self, root):
        self.root = root
        self.root.title("Feather Studio v1.1.8")
        self.root.geometry("1400x800")
        self.root.configure(bg="#0f0f0f")

        # Try to set feather icon
        try:
            icon_path = os.path.join(os.path.dirname(__file__), "feather_icon.png")
            if os.path.exists(icon_path):
                icon = tk.PhotoImage(file=icon_path)
                self.root.iconphoto(True, icon)
                self._icon = icon  # keep reference
        except Exception:
            pass

        # Track colors (distinct FL-style colors)
        self.track_colors = [
            "#4CAF50",  # green
            "#2196F3",  # blue
            "#FF9800",  # orange
            "#9C27B0",  # purple
            "#00BCD4",  # cyan
            "#F44336",  # red
            "#FFEB3B",  # yellow
            "#E91E63",  # pink
        ]

        # Tracks data: list of clips {path, start_time_sec, duration, color}
        self.tracks = [[] for _ in range(8)]
        self.imported = []          # list of (display_name, full_path)
        self.volumes = [0.8] * 8
        self.muted = [False] * 8
        self.is_playing = False
        self.is_recording = False
        self.mic_muted = True
        self.mic_recording = False
        self.mic_data = []
        self.current_mic_clip = None
        self.master_gain = 1.0
        self.bpm = 120.0
        self.left_level = 0.0
        self.right_level = 0.0
        self.current_tool = "Piano"
        self.drag_start = None
        self.rubber_band = None
        self.playhead_time = 0.0    # seconds
        self.pixels_per_second = 80
        self.last_update_time = None
        self.selected_track = 0
        self.selected_clips = []   # list of (track_idx, clip_dict) that are selected
        self.recording_notes = []
        self.effects_panel = None
        self.effects_clip = None

        # Audio
        self.channels = [pygame.mixer.Channel(i) for i in range(8)]
        for ch in self.channels:
            ch.set_volume(0.8)

        self.piano_sounds = {}
        self.preload_piano()
        self.metronome_click = self.generate_click()
        self.last_beat = -1  # for metronome tracking
        self.metronome_enabled = False  # off by default
        self.snap_enabled = True
        self.dragging_clips = None
        self.drag_mouse_offset = 0.0
        self.project_name = "Untitled Project"
        self.first_audio_imported = False  # for auto-BPM
        self.menu_dark_mode = False  # False = poop gray, True = dark #313338
        self.name_editing = False

        self.setup_ui()
        self.bind_keys()
        self.update_loop()
        self.show_menu()  # start on menu

    def preload_piano(self):
        notes = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B']
        for octave in [3, 4, 5]:
            for note in notes:
                name = f"{note}{octave}"
                freq = NOTE_FREQS[note] * (2 ** (octave - 4))
                arr = generate_realistic_piano(freq, duration=2.0)
                self.piano_sounds[name] = pygame.sndarray.make_sound(arr)

    def generate_click(self):
        """Short metronome click sound."""
        duration = 0.04
        n = int(SAMPLE_RATE * duration)
        t = np.linspace(0, duration, n, False)
        # High-frequency tick
        wave = np.sin(2 * np.pi * 1200 * t) * np.exp(-40 * t)
        wave = (wave * 0.5 * 32767).astype(np.int16)
        stereo = np.column_stack((wave, wave))
        return pygame.sndarray.make_sound(stereo)

    def setup_ui(self):
        # Container for the whole editor
        self.editor_frame = tk.Frame(self.root, bg="#0f0f0f")
        self.editor_frame.pack(fill="both", expand=True)

        # Project header bar
        header = tk.Frame(self.editor_frame, bg="#1a1a1a", height=40)
        header.pack(fill="x")
        header.pack_propagate(False)

        self.back_btn = tk.Button(header, text="← Back to Menu", command=self.back_to_menu,
                                  bg="#333", fg="white", font=("Segoe UI", 9), relief="flat")
        self.back_btn.pack(side="left", padx=8, pady=6)

        tk.Label(header, text="Project:", bg="#1a1a1a", fg="#aaa", font=("Segoe UI", 9)).pack(side="left", padx=(10, 4))
        self.project_name_var = tk.StringVar(value=self.project_name)
        self.project_entry = tk.Entry(header, textvariable=self.project_name_var, font=("Segoe UI", 11, "bold"),
                                       bg="#222", fg="white", insertbackground="white", relief="flat", width=30)
        self.project_entry.pack(side="left", padx=4, pady=6)
        self.project_entry.bind("<KeyRelease>", lambda e: setattr(self, "project_name", self.project_name_var.get()))
        self.project_entry.bind("<FocusIn>", self.on_name_focus_in)
        self.project_entry.bind("<FocusOut>", self.on_name_focus_out)
        self.project_entry.bind("<Return>", self.on_name_enter)
        self.project_entry.bind("<Escape>", self.on_name_escape)

        self.save_btn = tk.Button(header, text="💾 Save", command=self.save_project,
                                  bg="#4a148c", fg="white", font=("Segoe UI", 9, "bold"), relief="flat")
        self.save_btn.pack(side="right", padx=8, pady=6)

        # --- Toolbar ---
        toolbar = tk.Frame(self.editor_frame, bg="#1a1a1a", height=55)
        toolbar.pack(fill="x", padx=4, pady=4)

        style_btn = {"font": ("Segoe UI", 9, "bold"), "relief": "flat", "bd": 0, "padx": 10, "pady": 4}

        tk.Button(toolbar, text="Import Folder", command=self.import_folder,
                  bg="#2e7d32", fg="white", **style_btn).pack(side="left", padx=3)
        tk.Button(toolbar, text="Import Files", command=self.import_files,
                  bg="#1565c0", fg="white", **style_btn).pack(side="left", padx=3)

        self.play_btn = tk.Button(toolbar, text="▶ PLAY", command=self.toggle_play,
                                   bg="#e65100", fg="white", **style_btn)
        self.play_btn.pack(side="left", padx=8)
        tk.Button(toolbar, text="⏹ STOP", command=self.stop,
                  bg="#b71c1c", fg="white", **style_btn).pack(side="left", padx=3)

        self.rec_btn = tk.Button(toolbar, text="● REC", command=self.toggle_record,
                                  bg="#424242", fg="white", **style_btn)
        self.rec_btn.pack(side="left", padx=8)

        self.mic_btn = tk.Button(toolbar, text="🎤 MIC OFF", command=self.toggle_mic,
                                  bg="#333", fg="white", **style_btn)
        self.mic_btn.pack(side="left", padx=3)

        # BPM controls
        bpm_frame = tk.Frame(toolbar, bg="#1a1a1a")
        bpm_frame.pack(side="left", padx=12)
        tk.Label(bpm_frame, text="BPM", bg="#1a1a1a", fg="#aaa", font=("Segoe UI", 8)).pack(side="left")
        self.bpm_label = tk.Label(bpm_frame, text="120", bg="#1a1a1a", fg="#4caf50",
                                  font=("Segoe UI", 11, "bold"), width=4)
        self.bpm_label.pack(side="left", padx=4)
        self.bpm_slider = ttk.Scale(bpm_frame, from_=60, to=200, orient="horizontal",
                                     length=100, command=self.set_bpm)
        self.bpm_slider.set(120)
        self.bpm_slider.pack(side="left", padx=4)

        self.metro_btn = tk.Button(bpm_frame, text="Metronome OFF", command=self.toggle_metronome,
                                   bg="#333", fg="white", font=("Segoe UI", 8), relief="flat", padx=6)
        self.metro_btn.pack(side="left", padx=6)

        self.snap_btn = tk.Button(bpm_frame, text="Snap: ON", command=self.toggle_snap,
                                  bg="#4caf50", fg="white", font=("Segoe UI", 8), relief="flat", padx=6)
        self.snap_btn.pack(side="left", padx=6)

        tk.Button(toolbar, text="Export Song", command=self.export_song,
                  bg="#4a148c", fg="white", **style_btn).pack(side="left", padx=8)

        self.status = tk.Label(toolbar, text="Ready  |  Space = Play/Pause   Shift+P = Stop   ←→ = BPM   Double-click file/clip for effects",
                               bg="#1a1a1a", fg="#aaaaaa", font=("Segoe UI", 8))
        self.status.pack(side="right", padx=10)

        # --- Main ---
        main = tk.Frame(self.editor_frame, bg="#0f0f0f")
        main.pack(fill="both", expand=True, padx=4, pady=4)

        # Left - Files
        left = tk.Frame(main, bg="#161616", width=240)
        left.pack(side="left", fill="y")
        left.pack_propagate(False)
        tk.Label(left, text="AUDIO FILES", bg="#161616", fg="#cccccc",
                 font=("Segoe UI", 9, "bold")).pack(pady=6)
        self.file_list = tk.Listbox(left, bg="#111111", fg="#eeeeee",
                                     selectbackground="#4caf50", font=("Segoe UI", 9),
                                     relief="flat", highlightthickness=0)
        self.file_list.pack(fill="both", expand=True, padx=6, pady=4)
        self.file_list.bind("<Double-Button-1>", self.on_double_click_file)
        self.file_list.bind("<ButtonPress-1>", self.start_file_drag)
        self.file_list.bind("<B1-Motion>", self.do_file_drag)
        self.file_list.bind("<ButtonRelease-1>", self.end_file_drag)

        # Button under files that opens tools
        self.tools_open = False
        tk.Button(left, text="＋ Tools", bg="#2a2a2a", fg="white", relief="flat",
                  command=self.toggle_tools_panel).pack(fill="x", padx=6, pady=4)

        # Center - Timeline
        center = tk.Frame(main, bg="#0f0f0f")
        center.pack(side="left", fill="both", expand=True, padx=6)

        # Clickable timeline header (click to move playhead)
        header_frame = tk.Frame(center, bg="#1a1a1a", height=28)
        header_frame.pack(fill="x")
        header_frame.pack_propagate(False)

        self.header_canvas = tk.Canvas(header_frame, bg="#1a1a1a", height=28, highlightthickness=0)
        self.header_canvas.pack(fill="both", expand=True)
        self.header_canvas.create_text(8, 14, text="TIMELINE  (click to move playhead)", fill="#cccccc",
                                       anchor="w", font=("Segoe UI", 9, "bold"))
        self.header_canvas.bind("<Button-1>", self.on_header_click)

        self.canvas = tk.Canvas(center, bg="#0a0a0a", highlightthickness=0)
        self.hbar = ttk.Scrollbar(center, orient="horizontal", command=self.canvas.xview)
        vbar = ttk.Scrollbar(center, orient="vertical", command=self.canvas.yview)
        self.canvas.configure(xscrollcommand=self._on_timeline_xscroll, yscrollcommand=vbar.set)
        self.canvas.pack(side="top", fill="both", expand=True)
        self.hbar.pack(side="bottom", fill="x")
        vbar.pack(side="right", fill="y")

        self.canvas.bind("<Button-1>", self.on_canvas_click)
        self.canvas.bind("<B1-Motion>", self.on_canvas_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_canvas_release)
        self.canvas.bind("<Double-Button-1>", self.on_canvas_double_click)
        self.draw_timeline()

        # Right - Mixer + Master
        right = tk.Frame(main, bg="#161616", width=280)
        right.pack(side="right", fill="y")
        right.pack_propagate(False)

        tk.Label(right, text="TRACK MIXER", bg="#161616", fg="#cccccc",
                 font=("Segoe UI", 9, "bold")).pack(pady=4)
        mixer = tk.Frame(right, bg="#161616")
        mixer.pack(fill="x", padx=6)
        self.vol_sliders = []
        self.mute_btns = []
        for i in range(8):
            f = tk.Frame(mixer, bg="#161616")
            f.pack(fill="x", pady=1)
            tk.Label(f, text=f"T{i+1}", bg="#161616", fg="#888", width=3).pack(side="left")
            mute = tk.Button(f, text="M", width=2, bg="#333", fg="white", relief="flat",
                             command=lambda idx=i: self.toggle_mute(idx))
            mute.pack(side="left", padx=2)
            self.mute_btns.append(mute)
            vol = ttk.Scale(f, from_=0, to=1, orient="horizontal",
                            command=lambda v, idx=i: self.set_volume(idx, float(v)))
            vol.set(0.8)
            vol.pack(side="left", fill="x", expand=True, padx=2)
            self.vol_sliders.append(vol)
            # Reset to default 0.8
            tk.Button(f, text="↺", command=lambda idx=i, s=vol: (s.set(0.8), self.set_volume(idx, 0.8)),
                      bg="#222", fg="#888", font=("Segoe UI", 6), width=1, relief="flat").pack(side="left", padx=1)

        # Master volume + meters
        tk.Label(right, text="MASTER", bg="#161616", fg="#cccccc",
                 font=("Segoe UI", 9, "bold")).pack(pady=(12, 4))
        master_frame = tk.Frame(right, bg="#161616")
        master_frame.pack(fill="x", padx=8)
        self.left_meter = tk.Canvas(master_frame, height=12, bg="#111", highlightthickness=0)
        self.left_meter.pack(fill="x", pady=1)
        self.right_meter = tk.Canvas(master_frame, height=12, bg="#111", highlightthickness=0)
        self.right_meter.pack(fill="x", pady=1)
        tk.Label(right, text="Master Gain", bg="#161616", fg="#888", font=("Segoe UI", 8)).pack()
        master_ctrl = tk.Frame(right, bg="#161616")
        master_ctrl.pack(fill="x", padx=8)
        self.master_slider = ttk.Scale(master_ctrl, from_=0, to=2, orient="horizontal",
                                        command=self.set_master_gain)
        self.master_slider.set(1.0)
        self.master_slider.pack(side="left", fill="x", expand=True)
        tk.Button(master_ctrl, text="↺", command=lambda: (self.master_slider.set(1.0), self.set_master_gain(1.0)),
                  bg="#333", fg="#aaa", font=("Segoe UI", 7), width=2, relief="flat").pack(side="left", padx=2)

        # Tools dropdown
        tk.Label(right, text="TOOLS", bg="#161616", fg="#cccccc",
                 font=("Segoe UI", 9, "bold")).pack(pady=(12, 4))
        self.tool_var = tk.StringVar(value="Piano")
        tool_menu = ttk.Combobox(right, textvariable=self.tool_var, state="readonly",
                                 values=["Piano", "Drums", "Mic"])
        tool_menu.pack(fill="x", padx=8)
        tool_menu.bind("<<ComboboxSelected>>", self.on_tool_change)

        # Bottom tool area (starts empty — MIDI/effects only open when requested)
        self.tool_area = tk.Frame(self.editor_frame, bg="#1a1a1a", height=40)
        self.tool_area.pack(side="bottom", fill="x")
        self.tool_area.pack_propagate(False)
        tk.Label(self.tool_area, text="Double-click a track/clip for Effects  |  Select Piano/Drums tool then press M for MIDI editor",
                 bg="#1a1a1a", fg="#666", font=("Segoe UI", 8)).pack(pady=8)

    def set_bpm(self, val):
        self.bpm = float(val)
        self.bpm_label.config(text=f"{int(self.bpm)}")
        # Update the timeline grid to reflect new tempo
        if hasattr(self, "canvas"):
            self.draw_timeline()

    def toggle_metronome(self):
        self.metronome_enabled = not self.metronome_enabled
        if self.metronome_enabled:
            self.metro_btn.config(text="Metronome ON", bg="#4caf50")
            self.status.config(text="Metronome ON")
        else:
            self.metro_btn.config(text="Metronome OFF", bg="#333")
            self.status.config(text="Metronome OFF")

    def toggle_snap(self):
        self.snap_enabled = not self.snap_enabled
        if self.snap_enabled:
            self.snap_btn.config(text="Snap: ON", bg="#4caf50")
            self.status.config(text="Snap to grid ON")
        else:
            self.snap_btn.config(text="Snap: OFF", bg="#333")
            self.status.config(text="Free move (snap OFF)")

    def snap_time(self, t):
        """Snap a time (seconds) to the nearest beat if snap is enabled."""
        t = max(0.0, t)
        if not self.snap_enabled or self.bpm <= 0:
            return t
        sec_per_beat = 60.0 / self.bpm
        snapped = round(t / sec_per_beat) * sec_per_beat
        return max(0.0, snapped)

    def adjust_bpm(self, delta):
        new_bpm = max(60, min(200, self.bpm + delta))
        self.bpm_slider.set(new_bpm)
        self.set_bpm(new_bpm)

    def set_master_gain(self, val):
        self.master_gain = float(val)
        # Apply to all channels
        for i, ch in enumerate(self.channels):
            base = 0 if self.muted[i] else self.volumes[i]
            ch.set_volume(base * self.master_gain)

    def update_meters(self):
        """Real L/R stereo meters based on currently playing audio content."""
        target_l = 0.0
        target_r = 0.0
        if self.is_playing:
            for t_idx, clips in enumerate(self.tracks):
                if self.muted[t_idx] or not self.channels[t_idx].get_busy():
                    continue
                vol = self.volumes[t_idx] * self.master_gain
                for clip in clips:
                    start = clip.get("start", 0)
                    dur = clip.get("duration", 2.0)
                    if not (start <= self.playhead_time < start + dur):
                        continue
                    # Get audio array if available
                    arr = clip.get("audio_arr")
                    if arr is None:
                        # Fallback: try to load quickly if path exists
                        path = clip.get("processed_path") or clip.get("path")
                        if path and os.path.exists(path):
                            try:
                                snd = pygame.mixer.Sound(path)
                                raw = pygame.sndarray.array(snd)
                                if raw.ndim == 1:
                                    arr = np.column_stack((raw, raw)).astype(np.float32) / 32767.0
                                else:
                                    arr = raw.astype(np.float32) / 32767.0
                                clip["audio_arr"] = arr  # cache
                            except Exception:
                                arr = None
                        elif clip.get("is_piano"):
                            # Approximate level for piano (they decay)
                            age = self.playhead_time - start
                            if age < 1.5:
                                level = max(0, 0.6 * math.exp(-age * 2.0)) * vol
                                target_l += level
                                target_r += level * 0.98
                            continue
                    if arr is not None and len(arr) > 0:
                        pos = int((self.playhead_time - start) * SAMPLE_RATE)
                        win = 512
                        if 0 <= pos < len(arr):
                            end = min(pos + win, len(arr))
                            window = arr[pos:end]
                            if len(window) > 0:
                                rms_l = float(np.sqrt(np.mean(window[:, 0] ** 2)))
                                rms_r = float(np.sqrt(np.mean(window[:, 1] ** 2)))
                                target_l += rms_l * vol
                                target_r += rms_r * vol
                        break  # one active clip per track for meters
        # Smooth the meters
        self.left_level = self.left_level * 0.65 + min(1.0, target_l) * 0.35
        self.right_level = self.right_level * 0.65 + min(1.0, target_r) * 0.35
        for canvas, level in ((self.left_meter, self.left_level), (self.right_meter, self.right_level)):
            canvas.delete("all")
            w = max(canvas.winfo_width(), 160)
            canvas.create_rectangle(0, 0, w, 12, fill="#1a1a1a", outline="")
            fill_w = int(w * min(1.0, level))
            if fill_w > 0:
                color = "#4caf50" if level < 0.65 else ("#ffeb3b" if level < 0.85 else "#f44336")
                canvas.create_rectangle(0, 0, fill_w, 12, fill=color, outline="")

    def toggle_tools_panel(self):
        """Open/close a tools panel that appears over the file list."""
        if hasattr(self, "tools_panel") and self.tools_panel.winfo_exists():
            self.tools_panel.destroy()
            self.tools_open = False
            return
        # Overlay panel on the left side
        self.tools_panel = tk.Frame(self.root, bg="#1e1e1e", bd=1, relief="solid")
        self.tools_panel.place(x=10, y=120, width=220, height=280)
        tk.Label(self.tools_panel, text="TOOLS", bg="#1e1e1e", fg="white",
                 font=("Segoe UI", 10, "bold")).pack(pady=6)
        for tool in ["Piano", "Drums", "Mic", "Bass", "Guitar", "Synth"]:
            tk.Button(self.tools_panel, text=tool, bg="#333", fg="white", relief="flat",
                      command=lambda t=tool: self.add_tool_and_close(t)).pack(fill="x", padx=10, pady=2)
        tk.Button(self.tools_panel, text="Close", bg="#555", fg="white", relief="flat",
                  command=self.toggle_tools_panel).pack(fill="x", padx=10, pady=8)
        self.tools_open = True

    def start_file_drag(self, event):
        idx = self.file_list.nearest(event.y)
        if idx >= 0 and idx < self.file_list.size():
            self.drag_file_idx = idx
            self.drag_label = tk.Label(self.root, text=self.file_list.get(idx),
                                       bg="#4caf50", fg="white", font=("Segoe UI", 8))
            self.drag_label.place(x=event.x_root - self.root.winfo_rootx(),
                                  y=event.y_root - self.root.winfo_rooty())

    def do_file_drag(self, event):
        if hasattr(self, "drag_label") and self.drag_label:
            x = event.x_root - self.root.winfo_rootx()
            y = event.y_root - self.root.winfo_rooty()
            self.drag_label.place(x=x, y=y)

    def end_file_drag(self, event):
        if hasattr(self, "drag_label") and self.drag_label:
            self.drag_label.destroy()
            self.drag_label = None
        if not hasattr(self, "drag_file_idx") or self.drag_file_idx is None:
            return
        # Check if dropped on the timeline canvas
        cx = self.canvas.winfo_rootx()
        cy = self.canvas.winfo_rooty()
        cw = self.canvas.winfo_width()
        ch = self.canvas.winfo_height()
        if cx <= event.x_root <= cx + cw and cy <= event.y_root <= cy + ch:
            # Convert to canvas coords
            canvas_x = self.canvas.canvasx(event.x_root - cx)
            canvas_y = self.canvas.canvasy(event.y_root - cy)
            track = int(canvas_y // 55)
            if 0 <= track < 8:
                name, path = self.imported[self.drag_file_idx]
                # Temporarily set playhead so clip starts where dropped
                old = self.playhead_time
                self.playhead_time = max(0, canvas_x / self.pixels_per_second)
                self.place_clip_on_timeline(name, path, track=track)
                self.playhead_time = old
                self.status.config(text=f"Dropped '{name}' on Track {track+1}")
        self.drag_file_idx = None

    def add_tool_and_close(self, tool_name):
        # Also support drag from tools panel
        self.add_tool_clip(tool_name)
        if hasattr(self, "tools_panel") and self.tools_panel.winfo_exists():
            self.tools_panel.destroy()
            self.tools_open = False
        """Place a tool marker clip on the selected track."""
        clip = {
            "name": tool_name,
            "path": None,
            "start": self.playhead_time,
            "duration": 2.0,
            "is_piano": tool_name == "Piano",
            "waveform": None
        }
        self.tracks[self.selected_track].append(clip)
        self.draw_timeline()
        self.status.config(text=f"Added {tool_name} to Track {self.selected_track+1}")

    def on_tool_change(self, event=None):
        self.current_tool = self.tool_var.get()
        self.status.config(text=f"Tool set to {self.current_tool} — press M to open MIDI editor")

    def open_midi_editor(self, event=None):
        """Open MIDI editor only when requested (M key or button)."""
        if self.current_tool not in ("Piano", "Drums"):
            self.status.config(text="Switch to Piano or Drums tool first")
            return
        # Expand tool area and show MIDI
        self.tool_area.config(height=180)
        for w in self.tool_area.winfo_children():
            w.destroy()
        if self.current_tool == "Piano":
            self.build_piano_tool()
        else:
            self.build_drums_tool()
        self.status.config(text="MIDI editor opened")

    def build_piano_tool(self):
        top = tk.Frame(self.tool_area, bg="#1a1a1a")
        top.pack(fill="x", padx=6, pady=2)
        tk.Label(top, text="PIANO  |  Keys: A W S E D F T G Y H U J K   |  REC to place notes on track",
                 bg="#1a1a1a", fg="#ccc", font=("Segoe UI", 8)).pack(side="left")
        instruments = [
            "Grand Piano", "Upright Piano", "Electric Piano", "Rhodes", "Wurlitzer",
            "Organ", "Church Organ", "Strings", "Violin", "Cello", "Choir",
            "Synth Lead", "Synth Pad", "Brass", "Trumpet", "Saxophone",
            "Harpsichord", "Clavinet", "Marimba", "Vibraphone", "Acoustic Guitar",
            "Electric Guitar", "Bass", "Flute", "Clarinet"
        ]
        self.piano_inst = ttk.Combobox(top, values=instruments, state="readonly", width=18)
        self.piano_inst.set("Grand Piano")
        self.piano_inst.pack(side="right", padx=4)

        # MIDI editor canvas (BandLab / Soundtrap style)
        self.midi_canvas = tk.Canvas(self.tool_area, bg="#111111", height=110, highlightthickness=0)
        self.midi_canvas.pack(fill="both", expand=True, padx=4, pady=2)
        self.refresh_midi_editor()
        self.root.bind("<KeyPress>", self.on_piano_key)

    def refresh_midi_editor(self):
        if not hasattr(self, "midi_canvas") or not self.midi_canvas.winfo_exists():
            return
        self.midi_canvas.delete("all")
        track = self.selected_track
        clips = self.tracks[track]
        # Draw note rows
        notes = ["C", "D", "E", "F", "G", "A", "B"]
        h = 12
        for i, n in enumerate(notes):
            y = i * h
            self.midi_canvas.create_text(4, y + 6, text=n, fill="#555", anchor="w", font=("Segoe UI", 7))
        # Draw placed notes
        for clip in clips:
            if clip.get("is_piano") or "note" in clip or clip.get("name") in ["Kick", "Snare", "Hat", "Clap", "Tom", "Ride"]:
                x = clip["start"] * 40
                name = clip.get("note") or clip.get("name", "")
                row = 0
                for i, n in enumerate(notes):
                    if n in name:
                        row = i
                        break
                y = row * h
                self.midi_canvas.create_rectangle(x + 20, y + 1, x + 50, y + h - 1,
                                                   fill="#4caf50", outline="#fff")
                self.midi_canvas.create_text(x + 35, y + 6, text=name[:4], fill="white", font=("Segoe UI", 6))

    def on_piano_key(self, event):
        if self.name_editing or self.current_tool != "Piano":
            return
        mapping = {
            "a": "C4", "w": "C#4", "s": "D4", "e": "D#4", "d": "E4",
            "f": "F4", "t": "F#4", "g": "G4", "y": "G#4", "h": "A4",
            "u": "A#4", "j": "B4", "k": "C5"
        }
        note = mapping.get(event.keysym.lower())
        if note and note in self.piano_sounds:
            self.piano_sounds[note].play()
            if self.is_recording:
                self.add_piano_clip(note)
                self.refresh_midi_editor()

    def build_drums_tool(self):
        tk.Label(self.tool_area, text="DRUMS / BEAT MAKER  |  Click pads — notes appear on the selected track",
                 bg="#1a1a1a", fg="#ccc", font=("Segoe UI", 8)).pack(anchor="w", padx=6, pady=2)
        pads = tk.Frame(self.tool_area, bg="#1a1a1a")
        pads.pack(padx=6, pady=2)
        names = ["Kick", "Snare", "Hat", "Clap", "Tom", "Ride"]
        for i, name in enumerate(names):
            btn = tk.Button(pads, text=name, width=7, height=1, bg="#333", fg="white",
                            command=lambda n=name: self.play_drum(n))
            btn.grid(row=0, column=i, padx=2)
        # MIDI view for drums
        self.midi_canvas = tk.Canvas(self.tool_area, bg="#0d0d0d", height=70, highlightthickness=0)
        self.midi_canvas.pack(fill="x", padx=6, pady=4)
        self.refresh_midi_editor()

    def play_drum(self, name):
        """Better drum sounds (kick = low thump, snare/hat = noise)."""
        sr = SAMPLE_RATE
        dur = 0.25 if name != "Kick" else 0.35
        n = int(sr * dur)
        t = np.linspace(0, dur, n, False)
        if name == "Kick":
            freq = 80 * np.exp(-8 * t)
            wave = np.sin(2 * np.pi * freq * t) * np.exp(-6 * t)
        elif name in ("Snare", "Clap"):
            noise = np.random.uniform(-1, 1, n)
            tone = np.sin(2 * np.pi * 180 * t) * 0.4
            wave = (noise * 0.7 + tone) * np.exp(-10 * t)
        elif name == "Hat":
            noise = np.random.uniform(-1, 1, n)
            wave = noise * np.exp(-25 * t)
        else:
            freq = 140 * np.exp(-4 * t)
            wave = np.sin(2 * np.pi * freq * t) * np.exp(-5 * t)
        wave = (wave * 0.6 * 32767).astype(np.int16)
        stereo = np.column_stack((wave, wave))
        snd = pygame.sndarray.make_sound(stereo)
        snd.play()
        if self.is_recording:
            self.add_piano_clip(name)
            self.refresh_midi_editor()

    def build_mic_tool(self):
        tk.Label(self.tool_area, text="MICROPHONE", bg="#1a1a1a", fg="#ccc",
                 font=("Segoe UI", 9)).pack(anchor="w", padx=8, pady=4)
        tk.Label(self.tool_area, text="Device: Default Microphone", bg="#1a1a1a", fg="#888").pack(anchor="w", padx=8)
        self.mic_level = tk.Canvas(self.tool_area, height=16, bg="#111", highlightthickness=0)
        self.mic_level.pack(fill="x", padx=8, pady=4)
        tk.Button(self.tool_area, text="Record Mic to Track", bg="#c62828", fg="white",
                  command=self.record_mic_clip).pack(anchor="w", padx=8, pady=4)
        tk.Label(self.tool_area, text="(Requires sounddevice for real capture. Places a voice clip when used.)",
                 bg="#1a1a1a", fg="#666", font=("Segoe UI", 8)).pack(anchor="w", padx=8)

    def record_mic_clip(self):
        """Place a placeholder voice clip (real recording needs sounddevice)."""
        clip = {
            "name": "Mic Recording",
            "path": None,
            "start": self.playhead_time,
            "duration": 4.0,
            "is_piano": False,
            "waveform": [0.3 + 0.4 * abs(math.sin(i * 0.2)) for i in range(80)],
            "color": "#e91e63"
        }
        self.tracks[self.selected_track].append(clip)
        self.draw_timeline()
        self.status.config(text="Mic clip placed on track (enable sounddevice for live recording)")

    def on_canvas_drag(self, event):
        if self.dragging_clips:
            # Move selected clips
            canvas_x = self.canvas.canvasx(event.x)
            new_start_px = canvas_x - self.drag_mouse_offset
            new_start = max(0.0, new_start_px / self.pixels_per_second)
            # Apply delta from the first (primary) clip's original start
            primary_orig = self.dragging_clips[0][2]
            delta = new_start - primary_orig
            for t, c, orig in self.dragging_clips:
                raw = max(0.0, orig + delta)
                c["start"] = self.snap_time(raw)
            self.draw_timeline()
            return

        # Rubber-band selection
        if self.drag_start is None:
            self.drag_start = (self.canvas.canvasx(event.x), self.canvas.canvasy(event.y))
        x1, y1 = self.drag_start
        x2, y2 = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        if self.rubber_band:
            self.canvas.delete(self.rubber_band)
        self.rubber_band = self.canvas.create_rectangle(x1, y1, x2, y2, outline="#ffff00", dash=(2, 2), tags="select")

    def on_canvas_release(self, event):
        if self.dragging_clips:
            self.dragging_clips = None
            self.prepare_for_playback()
            self.status.config(text="Clip(s) moved")
            self.draw_timeline()
            return

        # Finish rubber-band selection
        if self.drag_start and self.rubber_band:
            x1, y1 = self.drag_start
            x2, y2 = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
            left, right = min(x1, x2), max(x1, x2)
            top, bottom = min(y1, y2), max(y1, y2)
            self.selected_clips = []
            track_h = 55
            for t_idx, clips in enumerate(self.tracks):
                y = t_idx * track_h
                if y + track_h < top or y > bottom:
                    continue
                for clip in clips:
                    cx = clip["start"] * self.pixels_per_second
                    cw = max(50, clip.get("duration", 2) * self.pixels_per_second)
                    if cx < right and cx + cw > left:
                        self.selected_clips.append((t_idx, clip))
            self.draw_timeline()
            self.status.config(text=f"Selected {len(self.selected_clips)} clip(s)")
        self.drag_start = None
        if self.rubber_band:
            self.canvas.delete(self.rubber_band)
            self.rubber_band = None
        """Return the required canvas width so we can scroll to the end of the longest clip."""
        max_end = 30.0  # minimum 30 seconds visible
        for clips in self.tracks:
            for clip in clips:
                end = clip["start"] + clip.get("duration", 2.0)
                if end > max_end:
                    max_end = end
        # Extra padding so the end of the clip isn't flush against the edge
        return int((max_end + 5.0) * self.pixels_per_second)

    def get_timeline_width(self):
        """Return the required canvas width so we can scroll to the end of the longest clip."""
        max_end = 30.0  # minimum 30 seconds visible
        for clips in self.tracks:
            for clip in clips:
                end = clip["start"] + clip.get("duration", 2.0)
                if end > max_end:
                    max_end = end
        # Extra padding so the end of the clip isn't flush against the edge
        return int((max_end + 5.0) * self.pixels_per_second)

    def darken_color(self, hex_color, factor=0.65):
        """Return a darker version of a hex color."""
        hex_color = hex_color.lstrip("#")
        r = int(hex_color[0:2], 16)
        g = int(hex_color[2:4], 16)
        b = int(hex_color[4:6], 16)
        r = int(r * factor)
        g = int(g * factor)
        b = int(b * factor)
        return f"#{r:02x}{g:02x}{b:02x}"

    def compute_waveform(self, path, num_points=300):
        """Real peak waveform from the actual audio file."""
        try:
            snd = pygame.mixer.Sound(path)
            arr = pygame.sndarray.array(snd)
            # Convert to mono absolute values
            if arr.ndim == 2:
                mono = np.abs(arr.mean(axis=1).astype(np.float32))
            else:
                mono = np.abs(arr.astype(np.float32))

            peak = mono.max()
            if peak > 0:
                mono /= peak

            # Proper peak downsampling (max in each bucket)
            if len(mono) > num_points:
                step = len(mono) / num_points
                peaks = []
                for i in range(num_points):
                    start = int(i * step)
                    end = int((i + 1) * step)
                    chunk = mono[start:end]
                    peaks.append(float(chunk.max()) if len(chunk) else 0.0)
                return peaks
            else:
                return list(mono)
        except Exception as e:
            print(f"Waveform error: {e}")
            return []

    def on_canvas_click(self, event):
        """Click a clip to select it (and prepare to drag), or click empty space to deselect / start rubber band."""
        canvas_x = self.canvas.canvasx(event.x)
        canvas_y = self.canvas.canvasy(event.y)
        track_h = 55
        track_idx = int(canvas_y // track_h)
        self.dragging_clips = None
        self.drag_start = None

        if not (0 <= track_idx < 8):
            self.selected_clips = []
            self.draw_timeline()
            return

        # Find if we clicked on a clip
        clicked_clip = None
        for clip in self.tracks[track_idx]:
            x = clip["start"] * self.pixels_per_second
            w = max(50, clip.get("duration", 2.0) * self.pixels_per_second)
            if x <= canvas_x <= x + w:
                clicked_clip = clip
                break

        if clicked_clip:
            shift_held = (event.state & 0x0001) != 0
            already = any(c is clicked_clip for _, c in self.selected_clips)

            if shift_held:
                if already:
                    self.selected_clips = [(t, c) for t, c in self.selected_clips if c is not clicked_clip]
                else:
                    self.selected_clips.append((track_idx, clicked_clip))
            else:
                if not already:
                    self.selected_clips = [(track_idx, clicked_clip)]

            # Prepare for drag if this clip is in the selection
            if any(c is clicked_clip for _, c in self.selected_clips):
                self.dragging_clips = []
                for t, c in self.selected_clips:
                    self.dragging_clips.append((t, c, c["start"]))
                self.drag_mouse_offset = canvas_x - (clicked_clip["start"] * self.pixels_per_second)
                self.status.config(text="Dragging clip(s)...")
            else:
                count = len(self.selected_clips)
                self.status.config(text=f"Selected {count} clip(s)" if count else "Selection cleared")
        else:
            # Empty space
            if not (event.state & 0x0001):
                self.selected_clips = []
                self.status.config(text="Selection cleared")
            self.drag_start = (canvas_x, canvas_y)

        self.draw_timeline()

    def select_all_clips(self, event=None):
        self.selected_clips = []
        for t_idx, clips in enumerate(self.tracks):
            for clip in clips:
                self.selected_clips.append((t_idx, clip))
        self.draw_timeline()
        self.status.config(text=f"Selected all ({len(self.selected_clips)} clips)")
        return "break"

    def delete_selected(self, event=None):
        if not self.selected_clips:
            return "break"
        # Remove selected clips from tracks
        to_remove = set(id(c) for _, c in self.selected_clips)
        for t_idx in range(8):
            self.tracks[t_idx] = [c for c in self.tracks[t_idx] if id(c) not in to_remove]
        count = len(self.selected_clips)
        self.selected_clips = []
        self.prepare_for_playback()
        self.draw_timeline()
        self.status.config(text=f"Deleted {count} clip(s)")
        return "break"

    def _on_timeline_xscroll(self, *args):
        """Sync the header canvas scroll with the main timeline."""
        if hasattr(self, "hbar"):
            self.hbar.set(*args)
        if hasattr(self, "header_canvas"):
            self.header_canvas.xview_moveto(args[0])

    def _sync_header_scroll(self, *args):
        pass  # header doesn't drive the scroll

    def on_header_click(self, event):
        """Click on the timeline header to jump the playhead there."""
        # Use the header's own canvas coordinates (already scrolled)
        canvas_x = self.header_canvas.canvasx(event.x)
        new_time = max(0.0, canvas_x / self.pixels_per_second)
        self.playhead_time = new_time
        self.last_beat = int(new_time / (60.0 / max(self.bpm, 1))) - 1

        for ch in self.channels:
            ch.stop()
        for clips in self.tracks:
            for clip in clips:
                clip.pop("triggered", None)

        self.draw_timeline()
        self.status.config(text=f"Playhead moved to {new_time:.1f}s")

        if self.is_playing:
            self.start_clips_at_current_position()
            self.status.config(text=f"Playing from {new_time:.1f}s")

    def draw_timeline(self):
        self.canvas.delete("all")
        track_h = 55
        total_w = self.get_timeline_width()

        for i in range(8):
            y = i * track_h
            bg = "#121212" if i % 2 == 0 else "#181818"
            self.canvas.create_rectangle(0, y, total_w, y + track_h, fill=bg, outline="#222")
            self.canvas.create_text(8, y + 28, text=f"Track {i+1}", fill="#666",
                                    anchor="w", font=("Segoe UI", 8))

        # Draw BPM-based beat grid (behind clips)
        if self.bpm > 0:
            seconds_per_beat = 60.0 / self.bpm
            pixels_per_beat = self.pixels_per_second * seconds_per_beat
            max_beats = int(total_w / max(pixels_per_beat, 1)) + 1
            for beat in range(max_beats + 1):
                x = beat * pixels_per_beat
                if x > total_w:
                    break
                if beat % 4 == 0:
                    self.canvas.create_line(x, 0, x, 8 * track_h, fill="#444444", width=1, tags="grid")
                    if beat > 0:
                        self.canvas.create_text(x + 3, 10, text=str(beat // 4 + 1), fill="#666", anchor="w", font=("Segoe UI", 6), tags="grid")
                else:
                    self.canvas.create_line(x, 0, x, 8 * track_h, fill="#2a2a2a", width=1, tags="grid")

        for i in range(8):
            y = i * track_h
            track_color = self.track_colors[i]

            for clip in self.tracks[i]:
                x = clip["start"] * self.pixels_per_second
                dur = clip.get("duration", 2.0)
                w = max(50, dur * self.pixels_per_second)

                color = track_color
                wave_color = self.darken_color(color, 0.25)
                is_selected = any(c is clip for _, c in self.selected_clips)
                outline_color = "#ffff00" if is_selected else "#ffffff"
                outline_width = 3 if is_selected else 1

                # Clip background
                self.canvas.create_rectangle(
                    x, y + 4, x + w, y + track_h - 4,
                    fill=color, outline=outline_color, width=outline_width, tags="clip"
                )

                # Real waveform (forced visible)
                waveform = clip.get("waveform")
                if not waveform or len(waveform) < 3:
                    # Always draw something so you can see it
                    waveform = [0.4 + 0.3 * abs(math.sin(i * 0.15)) for i in range(120)]

                mid_y = y + track_h / 2.0
                max_h = (track_h - 16) / 2.0
                points_upper = []
                points_lower = []
                n = len(waveform)
                for idx, amp in enumerate(waveform):
                    px = x + (idx / max(1, n - 1)) * w
                    amp_h = max(1, amp * max_h)
                    points_upper.append((px, mid_y - amp_h))
                    points_lower.append((px, mid_y + amp_h))

                if len(points_upper) > 1:
                    self.canvas.create_line(points_upper, fill=wave_color, width=2, tags="clip")
                    self.canvas.create_line(points_lower, fill=wave_color, width=2, tags="clip")

                # Clip name
                self.canvas.create_text(
                    x + 8, y + 15,
                    text=clip["name"][:20],
                    fill="white", anchor="w",
                    font=("Segoe UI", 7, "bold"), tags="clip"
                )

        # Playhead
        px = self.playhead_time * self.pixels_per_second
        self.playhead = self.canvas.create_line(px, 0, px, 8 * track_h, fill="#ff5722", width=2, tags="playhead")
        # Header playhead
        if hasattr(self, "header_canvas"):
            self.header_canvas.delete("playhead")
            self.header_canvas.create_line(px, 0, px, 28, fill="#ff5722", width=2, tags="playhead")

        self.canvas.configure(scrollregion=(0, 0, total_w, 8 * track_h))
        # Keep header scroll region in sync so it can move with the timeline
        if hasattr(self, "header_canvas"):
            self.header_canvas.configure(scrollregion=(0, 0, total_w, 28))

    def build_piano(self):
        notes_white = ['C', 'D', 'E', 'F', 'G', 'A', 'B']
        notes_black = ['C#', 'D#', None, 'F#', 'G#', 'A#', None]
        for oct in [3, 4, 5]:
            f = tk.Frame(self.piano_frame, bg="#161616")
            f.pack(side="left", padx=1)
            for i, n in enumerate(notes_white):
                btn = tk.Button(f, text=f"{n}{oct}", width=3, height=5,
                                bg="#f5f5f5", fg="black", relief="raised",
                                command=lambda name=f"{n}{oct}": self.play_note(name))
                btn.grid(row=1, column=i)
            # Black keys
            bf = tk.Frame(f, bg="#161616")
            bf.place(relx=0, rely=0, relwidth=1, relheight=0.62)
            for i, n in enumerate(notes_black):
                if n:
                    btn = tk.Button(bf, text=n, width=2, height=3,
                                    bg="#111", fg="white", relief="raised",
                                    command=lambda name=f"{n}{oct}": self.play_note(name))
                    btn.place(x=i*28 + 12, y=2)

    def play_note(self, note_name):
        if note_name in self.piano_sounds:
            self.piano_sounds[note_name].play()
            if self.is_recording:
                # Place a short piano clip on selected track at current playhead
                self.add_piano_clip(note_name)
            self.status.config(text=f"Piano: {note_name}")

    def add_piano_clip(self, note_name):
        track = self.selected_track
        start = self.playhead_time
        clip = {
            "name": note_name,
            "path": None,
            "start": start,
            "duration": 1.2,
            "is_piano": True,
            "note": note_name,
            "waveform": None
        }
        self.tracks[track].append(clip)
        self.prepare_for_playback()
        self.draw_timeline()
        if hasattr(self, "refresh_midi_editor"):
            self.refresh_midi_editor()

    def import_folder(self):
        folder = filedialog.askdirectory(title="Select audio folder")
        if not folder:
            return
        count = 0
        for ext in ("*.wav", "*.mp3", "*.ogg", "*.flac", "*.aiff"):
            for p in Path(folder).glob(ext):
                self.add_imported(str(p))
                count += 1
        self.status.config(text=f"Imported {count} files from folder")

    def import_files(self):
        files = filedialog.askopenfilenames(
            title="Select audio files",
            filetypes=[("Audio", "*.wav *.mp3 *.ogg *.flac *.aiff"), ("All", "*.*")]
        )
        for f in files:
            self.add_imported(f)
        self.status.config(text=f"Imported {len(files)} file(s)")

    def add_imported(self, path):
        name = os.path.basename(path)
        if any(p == path for _, p in self.imported):
            return
        self.imported.append((name, path))
        self.file_list.insert("end", name)

    def on_double_click_file(self, event):
        idx = self.file_list.curselection()
        if not idx:
            return
        name, path = self.imported[idx[0]]
        self.place_clip_on_timeline(name, path)

    def place_clip_on_timeline(self, name, path, track=None):
        if track is None:
            track = self.selected_track
        # Estimate duration (rough)
        try:
            snd = pygame.mixer.Sound(path)
            dur = snd.get_length()
            # Cache audio array for meters
            raw = pygame.sndarray.array(snd)
            if raw.ndim == 1:
                audio_arr = np.column_stack((raw, raw)).astype(np.float32) / 32767.0
            else:
                audio_arr = raw.astype(np.float32) / 32767.0
        except:
            dur = 4.0
            audio_arr = None
        # Generate real waveform right away
        waveform = self.compute_waveform(path) if path else []

        clip = {
            "name": name,
            "path": path,
            "start": self.playhead_time,
            "duration": dur,
            "is_piano": False,
            "waveform": waveform,
            "audio_arr": audio_arr
        }
        self.tracks[track].append(clip)
        self.prepare_for_playback()
        self.draw_timeline()
        self.status.config(text=f"Placed '{name}' on Track {track+1}")

        # Auto-set BPM from the first real audio file imported to the timeline
        if not self.first_audio_imported and path and os.path.exists(path):
            estimated = estimate_bpm(path)
            if estimated is not None:
                self.bpm = estimated
                self.bpm_slider.set(estimated)
                self.bpm_label.config(text=f"{int(estimated)}")
                self.draw_timeline()
                self.status.config(text=f"Placed '{name}' — BPM set to {int(estimated)} from audio")
            self.first_audio_imported = True

    def set_volume(self, track, vol):
        self.volumes[track] = vol
        self.channels[track].set_volume(0 if self.muted[track] else vol)

    def toggle_mute(self, track):
        self.muted[track] = not self.muted[track]
        btn = self.mute_btns[track]
        if self.muted[track]:
            btn.config(bg="#c62828")
            self.channels[track].set_volume(0)
        else:
            btn.config(bg="#333")
            self.channels[track].set_volume(self.volumes[track])

    def prepare_for_playback(self):
        """Reset audio state so the next Play reflects the current timeline exactly."""
        for ch in self.channels:
            ch.stop()
        for clips in self.tracks:
            for clip in clips:
                clip.pop("triggered", None)
        if self.is_playing:
            self.start_clips_at_current_position()

    def toggle_play(self):
        if self.is_playing:
            self.pause()
        else:
            self.play()

    def play(self):
        self.is_playing = True
        self.last_update_time = None
        self.last_beat = int(self.playhead_time / (60.0 / max(self.bpm, 1))) - 1
        self.prepare_for_playback()
        self.play_btn.config(text="⏸ PAUSE", bg="#f57c00")
        self.status.config(text="Playing...")

    def pause(self):
        self.is_playing = False
        for ch in self.channels:
            ch.pause()
        self.play_btn.config(text="▶ PLAY", bg="#e65100")
        self.status.config(text="Paused")

    def stop(self):
        self.is_playing = False
        self.playhead_time = 0.0
        self.last_beat = -1
        for ch in self.channels:
            ch.stop()
        # Reset triggered flags so clips can play again
        for clips in self.tracks:
            for clip in clips:
                clip.pop("triggered", None)
        self.play_btn.config(text="▶ PLAY", bg="#e65100")
        self.draw_timeline()
        self.status.config(text="Stopped")

    def toggle_record(self):
        self.is_recording = not self.is_recording
        if self.is_recording:
            self.rec_btn.config(bg="#c62828", text="● REC ON")
            self.status.config(text="Recording ON - play piano notes to place them")
        else:
            self.rec_btn.config(bg="#424242", text="● REC")
            self.status.config(text="Recording OFF")

    def update_loop(self):
        """Main animation / playback timing loop (real-time based)"""
        import time
        now = time.time()

        if self.is_playing:
            if self.last_update_time is None:
                self.last_update_time = now
            delta = now - self.last_update_time
            self.last_update_time = now

            # Move playhead by real elapsed time (no fixed delay)
            self.playhead_time += delta

            # Metronome: play click on each beat (only if enabled)
            if self.metronome_enabled and self.bpm > 0 and self.metronome_click:
                seconds_per_beat = 60.0 / self.bpm
                current_beat = int(self.playhead_time / seconds_per_beat)
                if current_beat > self.last_beat and current_beat >= 0:
                    self.metronome_click.play()
                    self.last_beat = current_beat

            px = self.playhead_time * self.pixels_per_second
            # Robust playhead update (handles redraws that delete the item)
            self.canvas.delete("playhead")
            self.playhead = self.canvas.create_line(px, 0, px, 440, fill="#ff5722", width=2, tags="playhead")
            # Also update header playhead indicator
            if hasattr(self, "header_canvas"):
                self.header_canvas.delete("playhead")
                self.header_canvas.create_line(px, 0, px, 28, fill="#ff5722", width=2, tags="playhead")

            # Trigger clips when the playhead reaches their start (robust to frame gaps)
            for t_idx, clips in enumerate(self.tracks):
                if self.muted[t_idx]:
                    continue
                for clip in clips:
                    start = clip["start"]
                    dur = clip.get("duration", 2.0)
                    end = start + dur
                    if (self.playhead_time >= start and
                        self.playhead_time < end and
                        not clip.get("triggered")):
                        clip["triggered"] = True
                        offset = max(0.0, self.playhead_time - start)
                        self.trigger_clip(t_idx, clip, offset_sec=offset)

            # Optional: auto-stop a bit after the last clip ends (no huge overrun delay)
            max_end = 0
            for clips in self.tracks:
                for c in clips:
                    max_end = max(max_end, c["start"] + c.get("duration", 0))
            if max_end > 0 and self.playhead_time > max_end + 1.0:
                self.stop()
                return
        else:
            self.last_update_time = None

        self.update_meters()
        self.root.after(16, self.update_loop)  # ~60 fps for smoother movement

    def trigger_clip(self, track_idx, clip, offset_sec=0.0):
        """Play a clip from the correct point in its source audio, ending at the clip's end."""
        try:
            if clip.get("is_piano"):
                note = clip.get("note")
                if note and note in self.piano_sounds:
                    self.channels[track_idx].play(self.piano_sounds[note])
                return

            arr = clip.get("audio_arr")
            if arr is None:
                play_path = clip.get("processed_path") or clip.get("path")
                if not play_path or not os.path.exists(play_path):
                    return
                snd = pygame.mixer.Sound(play_path)
                raw = pygame.sndarray.array(snd)
                if raw.ndim == 1:
                    arr = np.column_stack((raw, raw)).astype(np.float32) / 32767.0
                else:
                    arr = raw.astype(np.float32) / 32767.0
                clip["audio_arr"] = arr

            if arr is None or len(arr) == 0:
                return

            # source_offset = where this clip begins inside the original audio (seconds)
            source_offset = clip.get("source_offset", 0.0)
            # playback offset = how far into the clip we are
            total_offset = source_offset + max(0.0, offset_sec)
            start_sample = int(total_offset * SAMPLE_RATE)

            # how much of the clip is left to play
            clip_dur = clip.get("duration", 2.0)
            remaining = max(0.0, clip_dur - max(0.0, offset_sec))
            end_sample = start_sample + int(remaining * SAMPLE_RATE)

            if start_sample >= len(arr):
                return
            end_sample = min(end_sample, len(arr))
            if end_sample <= start_sample:
                return

            sliced = arr[start_sample:end_sample]
            if len(sliced) == 0:
                return

            sliced_int = np.clip(sliced * 32767.0, -32767, 32767).astype(np.int16)
            partial = pygame.sndarray.make_sound(sliced_int)
            self.channels[track_idx].set_volume(self.volumes[track_idx])
            self.channels[track_idx].play(partial)
        except Exception as e:
            print("Playback error:", e)

    def start_clips_at_current_position(self):
        """Start any clips that the playhead is currently inside, from the correct offset."""
        for t_idx, clips in enumerate(self.tracks):
            if self.muted[t_idx]:
                continue
            for clip in clips:
                start = clip["start"]
                end = start + clip.get("duration", 2.0)
                # If playhead is inside this clip, start it from the right offset
                if start <= self.playhead_time < end and not clip.get("triggered"):
                    clip["triggered"] = True
                    offset = self.playhead_time - start
                    self.trigger_clip(t_idx, clip, offset_sec=offset)

    def export_song(self):
        # Custom export dialog
        dialog = tk.Toplevel(self.root)
        dialog.title("Export Song")
        dialog.geometry("420x250")
        dialog.configure(bg="#1a1a1a")
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.resizable(False, False)

        # Center it
        dialog.update_idletasks()
        x = self.root.winfo_x() + (self.root.winfo_width() // 2) - 210
        y = self.root.winfo_y() + (self.root.winfo_height() // 2) - 110
        dialog.geometry(f"+{x}+{y}")

        tk.Label(dialog, text="Export your song", bg="#1a1a1a", fg="white",
                 font=("Segoe UI", 12, "bold")).pack(pady=(15, 10))

        # Filename
        name_frame = tk.Frame(dialog, bg="#1a1a1a")
        name_frame.pack(fill="x", padx=20, pady=5)
        tk.Label(name_frame, text="File name:", bg="#1a1a1a", fg="#ccc").pack(side="left")
        name_entry = tk.Entry(name_frame, font=("Segoe UI", 10), width=25)
        name_entry.insert(0, self.project_name or "Untitled Project")
        name_entry.pack(side="left", padx=8)
        name_entry.focus()
        name_entry.select_range(0, "end")

        # Format
        fmt_frame = tk.Frame(dialog, bg="#1a1a1a")
        fmt_frame.pack(pady=10)
        tk.Label(fmt_frame, text="Format:", bg="#1a1a1a", fg="#ccc").pack(side="left", padx=(0, 10))

        format_var = tk.StringVar(value="wav")

        # WAV (always available)
        tk.Radiobutton(fmt_frame, text="WAV", variable=format_var, value="wav",
                       bg="#1a1a1a", fg="white", selectcolor="#333",
                       activebackground="#1a1a1a", activeforeground="white",
                       font=("Segoe UI", 10)).pack(side="left", padx=8)

        # Separator
        tk.Label(fmt_frame, text="|", bg="#1a1a1a", fg="#666", font=("Segoe UI", 12)).pack(side="left", padx=4)

        # MP3 and M4A (need ffmpeg)
        for fmt in ["MP3", "M4A"]:
            tk.Radiobutton(fmt_frame, text=fmt, variable=format_var, value=fmt.lower(),
                           bg="#1a1a1a", fg="white", selectcolor="#333",
                           activebackground="#1a1a1a", activeforeground="white",
                           font=("Segoe UI", 10)).pack(side="left", padx=8)

        # Note about ffmpeg
        note = tk.Label(dialog, text="(to choose MP3 or M4A you need FFmpeg downloaded)",
                        bg="#1a1a1a", fg="#888", font=("Segoe UI", 8))
        note.pack(pady=(0, 5))

        def do_export():
            song_name = name_entry.get().strip()
            if not song_name:
                messagebox.showwarning("Name needed", "Please enter a song name.", parent=dialog)
                return
            fmt = format_var.get()
            # Clean the song name
            song_name = "".join(c for c in song_name if c.isalnum() or c in " _-")
            if not song_name:
                song_name = "Untitled"
            # Final filename: "Feather Studio" + 3 spaces + song name
            full_name = f"Feather Studio   {song_name}.{fmt}"

            # Ask where to save
            path = filedialog.asksaveasfilename(
                initialfile=full_name,
                defaultextension=f".{fmt}",
                filetypes=[(fmt.upper(), f"*.{fmt}")],
                title=f"Save as {fmt.upper()}",
                parent=dialog
            )
            if not path:
                return

            dialog.destroy()
            self._do_actual_export(path, fmt)

        btn_frame = tk.Frame(dialog, bg="#1a1a1a")
        btn_frame.pack(pady=15)
        tk.Button(btn_frame, text="Export", command=do_export,
                  bg="#4a148c", fg="white", font=("Segoe UI", 10, "bold"),
                  padx=20, pady=4, relief="flat").pack(side="left", padx=5)
        tk.Button(btn_frame, text="Cancel", command=dialog.destroy,
                  bg="#333", fg="white", font=("Segoe UI", 10),
                  padx=15, pady=4, relief="flat").pack(side="left", padx=5)

    def _do_actual_export(self, path, fmt):
        progress_win = tk.Toplevel(self.root)
        progress_win.title("Exporting...")
        progress_win.geometry("380x120")
        progress_win.configure(bg="#1a1a1a")
        progress_win.transient(self.root)
        progress_win.grab_set()

        tk.Label(progress_win, text=f"Exporting as {fmt.upper()}...", bg="#1a1a1a", fg="white",
                 font=("Segoe UI", 10)).pack(pady=10)
        bar = ttk.Progressbar(progress_win, mode="indeterminate", length=320)
        bar.pack(pady=5)
        bar.start(12)
        status_lbl = tk.Label(progress_win, text="Preparing mix...", bg="#1a1a1a", fg="#aaa")
        status_lbl.pack()
        self.root.update()

        try:
            # Find total length
            max_end = 5.0
            has_audio = False
            for clips in self.tracks:
                for c in clips:
                    end = c["start"] + c.get("duration", 2.0)
                    if end > max_end:
                        max_end = end
                    if c.get("path") or c.get("processed_path") or c.get("is_piano"):
                        has_audio = True

            if not has_audio:
                raise Exception("No audio clips to export. Add some audio or piano notes first.")

            total_samples = int(max_end * SAMPLE_RATE)
            # Write in chunks so we never allocate a giant array
            chunk_size = SAMPLE_RATE * 10  # 10 seconds at a time
            wav_path = path if fmt == "wav" else path.rsplit(".", 1)[0] + ".wav"

            status_lbl.config(text="Mixing & writing...")
            self.root.update()

            with wave.open(wav_path, "wb") as wf:
                wf.setnchannels(2)
                wf.setsampwidth(2)
                wf.setframerate(SAMPLE_RATE)

                pos = 0
                while pos < total_samples:
                    end_pos = min(pos + chunk_size, total_samples)
                    chunk_len = end_pos - pos
                    mix_chunk = np.zeros((chunk_len, 2), dtype=np.float32)

                    # Mix all clips that overlap this chunk
                    for t_idx, clips in enumerate(self.tracks):
                        if self.muted[t_idx]:
                            continue
                        vol = self.volumes[t_idx] * self.master_gain
                        for clip in clips:
                            clip_start = int(clip["start"] * SAMPLE_RATE)
                            clip_dur_samples = int(clip.get("duration", 2.0) * SAMPLE_RATE)
                            source_offset_samples = int(clip.get("source_offset", 0.0) * SAMPLE_RATE)

                            arr = clip.get("audio_arr")
                            if arr is None:
                                play_path = clip.get("processed_path") or clip.get("path")
                                if play_path and os.path.exists(play_path):
                                    try:
                                        snd = pygame.mixer.Sound(play_path)
                                        raw = pygame.sndarray.array(snd)
                                        if raw.ndim == 1:
                                            arr = np.column_stack((raw, raw)).astype(np.float32) / 32767.0
                                        else:
                                            arr = raw.astype(np.float32) / 32767.0
                                    except:
                                        arr = None
                                elif clip.get("is_piano") and clip.get("note") in self.piano_sounds:
                                    try:
                                        arr = pygame.sndarray.array(self.piano_sounds[clip["note"]]).astype(np.float32) / 32767.0
                                    except:
                                        arr = None

                            if arr is None or len(arr) == 0:
                                continue

                            arr = np.asarray(arr, dtype=np.float32)
                            if arr.ndim == 1:
                                arr = np.column_stack((arr, arr))
                            elif arr.shape[1] == 1:
                                arr = np.column_stack((arr[:, 0], arr[:, 0]))
                            elif arr.shape[1] > 2:
                                arr = arr[:, :2]

                            # Available source samples for this clip
                            src_start = source_offset_samples
                            src_end = min(len(arr), source_offset_samples + clip_dur_samples)
                            if src_start >= src_end:
                                continue

                            clip_end = clip_start + (src_end - src_start)

                            # Overlap with current chunk?
                            overlap_start = max(pos, clip_start)
                            overlap_end = min(end_pos, clip_end)
                            if overlap_start >= overlap_end:
                                continue

                            src_off = src_start + (overlap_start - clip_start)
                            dst_off = overlap_start - pos
                            length = overlap_end - overlap_start
                            mix_chunk[dst_off:dst_off + length] += arr[src_off:src_off + length] * float(vol)

                    # Normalize this chunk lightly and write
                    peak = np.max(np.abs(mix_chunk))
                    if peak > 1.0:
                        mix_chunk /= peak
                    mix_int = np.clip(mix_chunk * 28000, -32767, 32767).astype(np.int16)
                    wf.writeframes(mix_int.tobytes())

                    pos = end_pos
                    status_lbl.config(text=f"Writing... {int(pos / SAMPLE_RATE)}s / {int(total_samples / SAMPLE_RATE)}s")
                    self.root.update()

            final_path = wav_path

            # Convert if needed
            if fmt in ("mp3", "m4a"):
                import shutil
                if shutil.which("ffmpeg"):
                    status_lbl.config(text=f"Converting to {fmt.upper()}...")
                    self.root.update()
                    import subprocess
                    cmd = ["ffmpeg", "-y", "-i", wav_path, "-b:a", "192k", path]
                    result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
                    if result.returncode == 0 and os.path.exists(path):
                        final_path = path
                        try:
                            os.remove(wav_path)
                        except:
                            pass
                    else:
                        messagebox.showwarning("Conversion failed",
                                               f"Saved as WAV instead:\n{wav_path}", parent=progress_win)
                else:
                    messagebox.showinfo("FFmpeg needed",
                                        f"Saved as WAV:\n{wav_path}", parent=progress_win)

            bar.stop()
            progress_win.destroy()
            messagebox.showinfo("Export Complete", f"Song saved successfully:\n{final_path}")

        except Exception as e:
            import traceback
            print(traceback.format_exc())
            try:
                bar.stop()
                progress_win.destroy()
            except:
                pass
            messagebox.showerror("Export Error", f"Could not export:\n{str(e)}")

    def on_name_focus_in(self, event=None):
        """Disable hotkeys while editing the project name."""
        self.name_editing = True
        self.disable_hotkeys()
        self.status.config(text="Editing project name — hotkeys disabled")

    def on_name_focus_out(self, event=None):
        """Re-enable hotkeys and save the name when leaving the entry."""
        self.name_editing = False
        self.project_name = self.project_name_var.get().strip() or "Untitled Project"
        self.project_name_var.set(self.project_name)
        self.enable_hotkeys()
        self.root.title(f"Feather Studio v1.1.8 — {self.project_name}")
        self.status.config(text="Ready")

    def on_name_enter(self, event=None):
        """Enter saves the name and exits the entry."""
        self.project_name = self.project_name_var.get().strip() or "Untitled Project"
        self.project_name_var.set(self.project_name)
        self.root.focus_set()  # remove focus from the entry
        return "break"

    def on_name_escape(self, event=None):
        """Escape cancels and exits without changing (or just exits)."""
        self.root.focus_set()
        return "break"

    def disable_hotkeys(self):
        """Unbind all global hotkeys."""
        for seq in ("<space>", "<Shift-P>", "<Shift-p>", "<Delete>", "<BackSpace>",
                    "<Control-a>", "<c>", "<C>", "<m>", "<M>",
                    "<Left>", "<Right>", "<Shift-Left>", "<Shift-Right>"):
            self.root.unbind(seq)
        for i in range(1, 9):
            self.root.unbind(str(i))

    def enable_hotkeys(self):
        """Re-bind all global hotkeys."""
        self.bind_keys()

    def bind_keys(self):
        self.root.bind("<space>", lambda e: self.toggle_play())
        self.root.bind("<Shift-P>", lambda e: self.stop())
        self.root.bind("<Shift-p>", lambda e: self.stop())
        self.root.bind("<Delete>", self.delete_selected)
        self.root.bind("<BackSpace>", self.delete_selected)
        self.root.bind("<Control-a>", self.select_all_clips)
        self.root.bind("<c>", self.cut_selected)
        self.root.bind("<C>", self.cut_selected)
        self.root.bind("<m>", self.open_midi_editor)
        self.root.bind("<M>", self.open_midi_editor)
        # BPM adjustment with left/right arrows
        self.root.bind("<Left>", lambda e: self.adjust_bpm(-1))
        self.root.bind("<Right>", lambda e: self.adjust_bpm(1))
        self.root.bind("<Shift-Left>", lambda e: self.adjust_bpm(-5))
        self.root.bind("<Shift-Right>", lambda e: self.adjust_bpm(5))
        # Select track with number keys 1-8
        for i in range(8):
            self.root.bind(str(i+1), lambda e, idx=i: self.select_track(idx))

    def cut_selected(self, event=None):
        """Cut the selected clip at the current playhead position (C key)."""
        if not self.selected_clips:
            self.status.config(text="Select a clip first, then press C to cut")
            return "break"
        track_idx, clip = self.selected_clips[0]
        cut_time = self.playhead_time
        start = clip["start"]
        end = start + clip.get("duration", 2.0)
        if not (start < cut_time < end):
            self.status.config(text="Playhead must be inside the clip to cut")
            return "break"

        # Split into two clips
        left_dur = cut_time - start
        right_dur = end - cut_time

        left = dict(clip)
        left["duration"] = left_dur
        left["name"] = clip["name"] + " (L)"
        # left keeps the original source_offset

        right = dict(clip)
        right["start"] = cut_time
        right["duration"] = right_dur
        right["name"] = clip["name"] + " (R)"
        # right starts later in the source audio
        right["source_offset"] = clip.get("source_offset", 0.0) + left_dur
        if "waveform" in right:
            right["waveform"] = None  # will regenerate if needed

        # Replace original with the two pieces
        clips = self.tracks[track_idx]
        idx = clips.index(clip)
        clips[idx:idx+1] = [left, right]
        self.selected_clips = [(track_idx, left)]
        self.prepare_for_playback()
        self.draw_timeline()
        self.status.config(text="Clip cut at playhead")
        return "break"

    def toggle_mic(self):
        self.mic_muted = not self.mic_muted
        if self.mic_muted:
            self.mic_btn.config(text="🎤 MIC OFF", bg="#333")
            self.status.config(text="Microphone muted")
        else:
            self.mic_btn.config(text="🎤 MIC ON", bg="#c62828")
            self.status.config(text="Microphone ready — turn on REC to record voice")

    def on_clip_double_click(self, event):
        """Double-click a clip to open the effects panel."""
        # This is bound on root; we need to check if it was on the canvas
        # For simplicity, open effects for the currently selected clip
        if not self.selected_clips:
            return
        _, clip = self.selected_clips[0]
        self.open_effects_panel(clip)

    def open_effects_panel(self, clip):
        if self.effects_panel:
            self.effects_panel.destroy()
        self.effects_clip = clip
        panel = tk.Frame(self.root, bg="#1a1a1a", height=140)
        panel.pack(side="bottom", fill="x")
        panel.pack_propagate(False)
        self.effects_panel = panel

        tk.Label(panel, text=f"Effects — {clip['name'][:30]}", bg="#1a1a1a", fg="white",
                 font=("Segoe UI", 9, "bold")).pack(anchor="w", padx=10, pady=4)

        controls = tk.Frame(panel, bg="#1a1a1a")
        controls.pack(fill="x", padx=10)

        def add_slider(label, key, from_, to, default):
            f = tk.Frame(controls, bg="#1a1a1a")
            f.pack(side="left", padx=6)
            top = tk.Frame(f, bg="#1a1a1a")
            top.pack()
            tk.Label(top, text=label, bg="#1a1a1a", fg="#aaa", font=("Segoe UI", 8)).pack(side="left")
            val = clip.get(key, default)
            scale = ttk.Scale(f, from_=from_, to=to, orient="horizontal", length=110)
            scale.set(val)
            # Reset button
            def make_reset(k=key, d=default, s=scale):
                def do_reset():
                    s.set(d)
                    self.apply_effect(clip, k, d)
                return do_reset
            reset_btn = tk.Button(top, text="↺", command=make_reset(), bg="#333", fg="#aaa",
                                   font=("Segoe UI", 7), width=2, relief="flat", padx=0, pady=0)
            reset_btn.pack(side="left", padx=2)
            scale.pack()
            scale.bind("<ButtonRelease-1>", lambda e, k=key, s=scale: self.apply_effect(clip, k, s.get()))
            # Double-click slider also resets
            scale.bind("<Double-Button-1>", lambda e, k=key, d=default, s=scale: (s.set(d), self.apply_effect(clip, k, d)))
            return scale

        add_slider("Bass", "bass", -12, 12, 0)
        add_slider("Treble", "treble", -12, 12, 0)
        add_slider("Speed", "speed", 0.5, 2.0, 1.0)
        add_slider("Gain", "gain", -12, 12, 0)
        add_slider("Pitch", "pitch", -12, 12, 0)
        add_slider("Reverb", "reverb", 0.0, 1.0, 0.0)
        add_slider("Pan", "pan", -1.0, 1.0, 0.0)  # -1 = 100% L, 0 = Center, 1 = 100% R

        # Labels for pan extremes
        pan_info = tk.Label(panel, text="Pan:  ← 100% L   |   Center   |   100% R →", 
                            bg="#1a1a1a", fg="#666", font=("Segoe UI", 7))
        pan_info.pack(anchor="w", padx=10)

        tk.Button(panel, text="Close", command=self.close_effects,
                  bg="#333", fg="white", relief="flat").pack(side="right", padx=10, pady=4)

    def apply_effect(self, clip, key, value):
        """Actually process the audio with the new effect value."""
        if self.is_playing:
            self.stop()

        clip[key] = float(value)
        self.status.config(text=f"Applying {key}...")
        self.root.update()

        if clip.get("is_piano") or not clip.get("path"):
            self.status.config(text=f"{key.capitalize()} set")
            return

        try:
            # Load original
            snd = pygame.mixer.Sound(clip["path"])
            raw = pygame.sndarray.array(snd)
            if raw.ndim == 1:
                arr = np.column_stack((raw, raw)).astype(np.float32)
            else:
                arr = raw.astype(np.float32)
            arr = arr / 32767.0

            # Process
            arr = self.process_audio(arr, clip)

            # Make sure it's valid for pygame
            arr = np.ascontiguousarray(arr)
            arr_int = np.clip(arr * 32767.0, -32767, 32767).astype(np.int16)
            # Cache float array for meters
            clip["audio_arr"] = arr.astype(np.float32)

            # Write temp WAV
            import tempfile
            fd, tmp_path = tempfile.mkstemp(suffix=".wav")
            os.close(fd)
            with wave.open(tmp_path, "wb") as wf:
                wf.setnchannels(2)
                wf.setsampwidth(2)
                wf.setframerate(SAMPLE_RATE)
                wf.writeframes(arr_int.tobytes())

            # Update clip
            clip["processed_path"] = tmp_path
            try:
                new_snd = pygame.mixer.Sound(tmp_path)
                clip["duration"] = new_snd.get_length()
            except:
                pass
            clip["waveform"] = self.compute_waveform(tmp_path)

            self.prepare_for_playback()
            self.draw_timeline()
            self.status.config(text=f"{key.capitalize()} applied")
        except Exception as e:
            self.status.config(text=f"Effect failed: {str(e)[:60]}")
            print("Effect error:", e)

    def process_audio(self, arr, clip):
        """Memory-friendly audio processing."""
        # Work on a copy, keep it float32
        arr = arr.astype(np.float32, copy=True)
        if arr.ndim == 1:
            arr = np.column_stack((arr, arr))

        # Gain (dB style: negative = quieter, positive = louder)
        gain_db = float(clip.get("gain", 0))
        if abs(gain_db) > 0.1:
            factor = 10 ** (gain_db / 20.0)
            arr *= factor

        # Bass: positive boosts lows, negative reduces lows
        bass = float(clip.get("bass", 0))
        if abs(bass) > 0.1:
            # Simple low-pass via averaging (memory light)
            low = arr.copy()
            for _ in range(3):
                low[1:-1] = (low[:-2] + low[1:-1] + low[2:]) / 3.0
            amount = bass / 12.0
            arr = arr + low * amount

        # Treble: positive boosts highs, negative reduces highs
        treble = float(clip.get("treble", 0))
        if abs(treble) > 0.1:
            # Crude high-pass
            high = arr.copy()
            high[1:-1] = arr[1:-1] - (arr[:-2] + arr[2:]) * 0.5
            amount = treble / 12.0
            arr = arr + high * amount

        # Speed
        speed = float(clip.get("speed", 1.0))
        if abs(speed - 1.0) > 0.02 and 0.25 <= speed <= 4.0:
            new_len = max(100, int(len(arr) / speed))
            # Resample carefully to avoid huge temps
            idx = np.linspace(0, len(arr) - 1, new_len)
            left = np.interp(idx, np.arange(len(arr)), arr[:, 0])
            right = np.interp(idx, np.arange(len(arr)), arr[:, 1])
            arr = np.column_stack((left, right)).astype(np.float32)

        # Pitch (resample approximation)
        pitch = float(clip.get("pitch", 0))
        if abs(pitch) > 0.1:
            factor = 2.0 ** (pitch / 12.0)
            new_len = max(100, int(len(arr) / factor))
            idx = np.linspace(0, len(arr) - 1, new_len)
            left = np.interp(idx, np.arange(len(arr)), arr[:, 0])
            right = np.interp(idx, np.arange(len(arr)), arr[:, 1])
            arr = np.column_stack((left, right)).astype(np.float32)

        # Pan: -1 = 100% Left, 0 = Center, 1 = 100% Right
        pan = float(clip.get("pan", 0.0))
        if abs(pan) > 0.01:
            # Constant-power panning
            angle = (pan + 1.0) * (math.pi / 4.0)
            l_gain = math.cos(angle)
            r_gain = math.sin(angle)
            arr[:, 0] *= l_gain
            arr[:, 1] *= r_gain

        # Reverb (simple multi-delay)
        reverb = float(clip.get("reverb", 0.0))
        if reverb > 0.02:
            arr = self.apply_simple_reverb(arr, reverb)

        # Prevent extreme clipping
        peak = np.max(np.abs(arr))
        if peak > 1.0:
            arr /= peak

        return arr

    def apply_simple_reverb(self, arr, strength):
        """Simple multi-tap delay reverb, memory-light."""
        if strength < 0.01 or len(arr) < 100:
            return arr
        wet = np.zeros_like(arr)
        delays = [
            (int(0.029 * SAMPLE_RATE), 0.42),
            (int(0.047 * SAMPLE_RATE), 0.28),
            (int(0.071 * SAMPLE_RATE), 0.18),
            (int(0.097 * SAMPLE_RATE), 0.11),
        ]
        for delay, gain in delays:
            if delay < len(arr):
                wet[delay:] += arr[:-delay] * gain
        # Mix dry/wet
        dry_gain = 1.0 - strength * 0.55
        wet_gain = strength * 0.75
        out = arr * dry_gain + wet * wet_gain
        # Soft limit
        peak = np.max(np.abs(out))
        if peak > 1.0:
            out /= peak
        return out.astype(np.float32)

    def close_effects(self):
        if self.effects_panel:
            self.effects_panel.destroy()
            self.effects_panel = None
            self.effects_clip = None

    def on_canvas_double_click(self, event):
        """Double-click a track/clip on the timeline to open effects."""
        canvas_x = self.canvas.canvasx(event.x)
        canvas_y = self.canvas.canvasy(event.y)
        track_h = 55
        track_idx = int(canvas_y // track_h)
        if not (0 <= track_idx < 8):
            return
        self.selected_track = track_idx
        # Prefer the clip under the cursor
        for clip in self.tracks[track_idx]:
            x = clip["start"] * self.pixels_per_second
            w = max(50, clip.get("duration", 2.0) * self.pixels_per_second)
            if x <= canvas_x <= x + w:
                self.selected_clips = [(track_idx, clip)]
                self.draw_timeline()
                self.open_effects_panel(clip)
                return
        # Otherwise open effects for the first clip on the track (if any)
        if self.tracks[track_idx]:
            clip = self.tracks[track_idx][0]
            self.selected_clips = [(track_idx, clip)]
            self.draw_timeline()
            self.open_effects_panel(clip)
            return
        self.status.config(text=f"Track {track_idx+1} has no clips for effects")

    def select_track(self, idx):
        self.selected_track = idx
        self.status.config(text=f"Selected Track {idx+1}")

    def show_menu(self):
        """Show the main menu screen."""
        if hasattr(self, "editor_frame"):
            self.editor_frame.pack_forget()
        if hasattr(self, "menu_frame") and self.menu_frame.winfo_exists():
            self.menu_frame.destroy()

        # Colors based on mode
        if self.menu_dark_mode:
            bg_color = "#313338"
            text_color = "#A0A0A0"  # pure perfect gray
            feather_color = "#A0A0A0"
        else:
            bg_color = "#8A7A6A"  # gray poop color
            text_color = "#D3D3D3"
            feather_color = "#D3D3D3"

        self.menu_frame = tk.Frame(self.root, bg=bg_color)
        self.menu_frame.pack(fill="both", expand=True)

        # Center content
        center = tk.Frame(self.menu_frame, bg=bg_color)
        center.place(relx=0.5, rely=0.5, anchor="center")

        # Simple vertical feather drawing
        canvas = tk.Canvas(center, width=120, height=280, bg=bg_color, highlightthickness=0)
        canvas.pack(pady=10)
        # Shaft
        canvas.create_line(60, 20, 60, 250, fill=feather_color, width=4)
        # Barbs (simple leaves)
        for i in range(15):
            y = 40 + i * 12
            width = 30 - abs(i - 7) * 2
            canvas.create_line(60, y, 60 - width, y + 6, fill=feather_color, width=2)
            canvas.create_line(60, y, 60 + width, y + 6, fill=feather_color, width=2)
        # Tip
        canvas.create_polygon(60, 10, 50, 30, 70, 30, fill=feather_color, outline="")

        tk.Label(center, text="Feather Studio", bg=bg_color, fg=text_color,
                 font=("Segoe UI", 28, "bold")).pack(pady=20)

        btn_style = {"font": ("Segoe UI", 12, "bold"), "relief": "flat", "padx": 30, "pady": 10, "width": 18}

        tk.Button(center, text="New Project", command=self.new_project,
                  bg="#4CAF50", fg="white", **btn_style).pack(pady=8)
        tk.Button(center, text="Open Project", command=self.open_project,
                  bg="#1565c0", fg="white", **btn_style).pack(pady=8)
        tk.Button(center, text="Quit", command=self.root.quit,
                  bg="#b71c1c", fg="white", **btn_style).pack(pady=8)

        # Dark mode toggle
        mode_text = "Light Mode" if self.menu_dark_mode else "Dark Mode"
        tk.Button(center, text=mode_text, command=self.toggle_menu_dark_mode,
                  bg="#555", fg="white", font=("Segoe UI", 9), relief="flat", padx=15, pady=4).pack(pady=(15, 5))

        self.root.title("Feather Studio v1.1.8 — Menu")

    def toggle_menu_dark_mode(self):
        self.menu_dark_mode = not self.menu_dark_mode
        self.show_menu()  # refresh menu with new colors

    def show_new_project_splash(self):
        """Brief splash when creating a new project."""
        if self.menu_dark_mode:
            bg_color = "#313338"
            text_color = "#A0A0A0"
            feather_color = "#A0A0A0"
            sub_color = "#888888"
        else:
            bg_color = "#8A7A6A"
            text_color = "#D3D3D3"
            feather_color = "#D3D3D3"
            sub_color = "#AAAAAA"

        splash = tk.Toplevel(self.root)
        splash.title("New Project")
        splash.geometry("500x400")
        splash.configure(bg=bg_color)
        splash.transient(self.root)
        splash.grab_set()

        # Center
        splash.update_idletasks()
        x = self.root.winfo_x() + (self.root.winfo_width() // 2) - 250
        y = self.root.winfo_y() + (self.root.winfo_height() // 2) - 200
        splash.geometry(f"+{x}+{y}")

        canvas = tk.Canvas(splash, width=120, height=220, bg=bg_color, highlightthickness=0)
        canvas.pack(pady=20)
        canvas.create_line(60, 10, 60, 200, fill=feather_color, width=4)
        for i in range(12):
            yb = 30 + i * 12
            w = 28 - abs(i - 5) * 2
            canvas.create_line(60, yb, 60 - w, yb + 5, fill=feather_color, width=2)
            canvas.create_line(60, yb, 60 + w, yb + 5, fill=feather_color, width=2)
        canvas.create_polygon(60, 5, 48, 25, 72, 25, fill=feather_color)

        tk.Label(splash, text="Feather Studio", bg=bg_color, fg=text_color,
                 font=("Segoe UI", 22, "bold")).pack(pady=10)
        tk.Label(splash, text="Creating new project...", bg=bg_color, fg=sub_color,
                 font=("Segoe UI", 11)).pack(pady=5)

        splash.after(1200, splash.destroy)

    def new_project(self):
        self.show_new_project_splash()
        # Reset state
        self.tracks = [[] for _ in range(8)]
        self.imported = []
        self.file_list.delete(0, "end")
        self.volumes = [0.8] * 8
        self.muted = [False] * 8
        self.bpm = 120.0
        self.bpm_slider.set(120)
        self.bpm_label.config(text="120")
        self.project_name = "Untitled Project"
        self.project_name_var.set(self.project_name)
        self.first_audio_imported = False
        self.playhead_time = 0.0
        self.is_playing = False
        self.selected_clips = []
        self.prepare_for_playback()
        self.draw_timeline()
        self.show_editor()

    def show_editor(self):
        if hasattr(self, "menu_frame") and self.menu_frame.winfo_exists():
            self.menu_frame.pack_forget()
        self.editor_frame.pack(fill="both", expand=True)
        self.root.title(f"Feather Studio v1.1.8 — {self.project_name}")

    def back_to_menu(self):
        if self.is_playing:
            self.stop()
        self.editor_frame.pack_forget()
        self.show_menu()

    def save_project(self):
        name = self.project_name_var.get().strip() or "Untitled Project"
        self.project_name = name
        path = filedialog.asksaveasfilename(
            title="Save Project",
            initialfile=f"{name}.FeatherM",
            defaultextension=".FeatherM",
            filetypes=[("Feather Music", "*.FeatherM"), ("All", "*.*")]
        )
        if not path:
            return
        try:
            import json
            data = {
                "name": name,
                "bpm": self.bpm,
                "volumes": self.volumes,
                "muted": self.muted,
                "imported": self.imported,
                "tracks": []
            }
            for track in self.tracks:
                tdata = []
                for clip in track:
                    c = {
                        "name": clip.get("name"),
                        "path": clip.get("path"),
                        "start": clip.get("start"),
                        "duration": clip.get("duration"),
                        "is_piano": clip.get("is_piano", False),
                        "note": clip.get("note"),
                    }
                    tdata.append(c)
                data["tracks"].append(tdata)
            with open(path, "w") as f:
                json.dump(data, f, indent=2)
            self.status.config(text=f"Project saved: {os.path.basename(path)}")
            messagebox.showinfo("Saved", f"Project saved successfully:\n{path}")
        except Exception as e:
            messagebox.showerror("Save Error", str(e))

    def open_project(self):
        path = filedialog.askopenfilename(
            title="Open Project",
            filetypes=[("Feather Music", "*.FeatherM"), ("All", "*.*")]
        )
        if not path:
            return
        try:
            import json
            with open(path, "r") as f:
                data = json.load(f)
            self.project_name = data.get("name", "Untitled")
            self.project_name_var.set(self.project_name)
            self.bpm = data.get("bpm", 120)
            self.bpm_slider.set(self.bpm)
            self.bpm_label.config(text=str(int(self.bpm)))
            self.volumes = data.get("volumes", [0.8]*8)
            self.muted = data.get("muted", [False]*8)
            self.imported = data.get("imported", [])
            self.file_list.delete(0, "end")
            for name, p in self.imported:
                self.file_list.insert("end", name)
            self.tracks = [[] for _ in range(8)]
            for t_idx, tdata in enumerate(data.get("tracks", [])):
                for c in tdata:
                    clip = {
                        "name": c.get("name", "clip"),
                        "path": c.get("path"),
                        "start": c.get("start", 0),
                        "duration": c.get("duration", 2),
                        "is_piano": c.get("is_piano", False),
                        "note": c.get("note"),
                        "waveform": None
                    }
                    if clip["path"] and os.path.exists(clip["path"]):
                        clip["waveform"] = self.compute_waveform(clip["path"])
                    self.tracks[t_idx].append(clip)
            self.first_audio_imported = True  # don't override BPM
            self.prepare_for_playback()
            self.draw_timeline()
            self.show_editor()
            self.status.config(text=f"Opened project: {self.project_name}")
        except Exception as e:
            messagebox.showerror("Open Error", str(e))

def main():
    root = tk.Tk()
    # Darker ttk style
    style = ttk.Style()
    style.theme_use("clam")
    app = MusicMaker(root)
    root.mainloop()

if __name__ == "__main__":
    main()
