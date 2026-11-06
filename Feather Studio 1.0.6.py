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

class MusicMaker:
    def __init__(self, root):
        self.root = root
        self.root.title("Feather Studio v1.0.6")
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
        self.playhead_time = 0.0    # seconds
        self.pixels_per_second = 80
        self.selected_track = 0
        self.selected_clips = []   # list of (track_idx, clip_dict) that are selected
        self.recording_notes = []

        # Audio
        self.channels = [pygame.mixer.Channel(i) for i in range(8)]
        for ch in self.channels:
            ch.set_volume(0.8)

        self.piano_sounds = {}
        self.preload_piano()

        self.setup_ui()
        self.bind_keys()
        self.update_loop()

    def preload_piano(self):
        notes = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B']
        for octave in [3, 4, 5]:
            for note in notes:
                name = f"{note}{octave}"
                freq = NOTE_FREQS[note] * (2 ** (octave - 4))
                arr = generate_realistic_piano(freq, duration=2.0)
                self.piano_sounds[name] = pygame.sndarray.make_sound(arr)

    def setup_ui(self):
        # --- Toolbar ---
        toolbar = tk.Frame(self.root, bg="#1a1a1a", height=55)
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

        tk.Button(toolbar, text="Export Song", command=self.export_song,
                  bg="#4a148c", fg="white", **style_btn).pack(side="left", padx=8)

        self.status = tk.Label(toolbar, text="Ready  |  Space = Play/Pause   Shift+P = Stop   Double-click file = place on timeline",
                               bg="#1a1a1a", fg="#aaaaaa", font=("Segoe UI", 8))
        self.status.pack(side="right", padx=10)

        # --- Main ---
        main = tk.Frame(self.root, bg="#0f0f0f")
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
        hbar = ttk.Scrollbar(center, orient="horizontal", command=self.canvas.xview)
        vbar = ttk.Scrollbar(center, orient="vertical", command=self.canvas.yview)
        self.canvas.configure(xscrollcommand=hbar.set, yscrollcommand=vbar.set)
        self.canvas.pack(side="top", fill="both", expand=True)
        hbar.pack(side="bottom", fill="x")
        vbar.pack(side="right", fill="y")

        self.canvas.bind("<Button-1>", self.on_canvas_click)
        self.draw_timeline()

        # Right - Piano + track controls
        right = tk.Frame(main, bg="#161616", width=320)
        right.pack(side="right", fill="y")
        right.pack_propagate(False)

        # Track mixer
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
            vol.pack(side="left", fill="x", expand=True, padx=4)
            self.vol_sliders.append(vol)

        # Piano
        tk.Label(right, text="PIANO", bg="#161616", fg="#cccccc",
                 font=("Segoe UI", 9, "bold")).pack(pady=(10, 4))
        self.piano_frame = tk.Frame(right, bg="#161616")
        self.piano_frame.pack(fill="both", expand=True, padx=6, pady=4)
        self.build_piano()

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
        """Click a clip to select it, or click empty space to deselect."""
        canvas_x = self.canvas.canvasx(event.x)
        canvas_y = self.canvas.canvasy(event.y)
        track_h = 55
        track_idx = int(canvas_y // track_h)
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
            shift_held = (event.state & 0x0001) != 0  # Shift key
            already = any(c is clicked_clip for _, c in self.selected_clips)

            if shift_held:
                # Multi-select: add or remove from selection
                if already:
                    self.selected_clips = [(t, c) for t, c in self.selected_clips if c is not clicked_clip]
                else:
                    self.selected_clips.append((track_idx, clicked_clip))
            else:
                # Normal click: single select
                if already and len(self.selected_clips) == 1:
                    self.selected_clips = []
                else:
                    self.selected_clips = [(track_idx, clicked_clip)]

            count = len(self.selected_clips)
            self.status.config(text=f"Selected {count} clip(s)" if count else "Selection cleared")
        else:
            # Clicked empty space → deselect all (unless shift is held)
            if not (event.state & 0x0001):
                self.selected_clips = []
                self.status.config(text="Selection cleared")

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
        self.draw_timeline()
        self.status.config(text=f"Deleted {count} clip(s)")
        return "break"

    def on_header_click(self, event):
        """Click on the timeline header to jump the playhead there."""
        # Account for horizontal scroll
        canvas_x = self.canvas.canvasx(event.x)
        # Convert pixels to time
        new_time = max(0.0, canvas_x / self.pixels_per_second)
        self.playhead_time = new_time

        # Stop any currently playing audio so it restarts cleanly from the new position
        for ch in self.channels:
            ch.stop()

        # Reset triggered flags so clips can trigger again from the new position
        for clips in self.tracks:
            for clip in clips:
                clip.pop("triggered", None)

        # Update playhead position immediately
        px = self.playhead_time * self.pixels_per_second
        if hasattr(self, "playhead"):
            self.canvas.coords(self.playhead, px, 0, px, 8 * 55)

        self.status.config(text=f"Playhead moved to {new_time:.1f}s")

        # If we were playing, continue from the new spot
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

        self.canvas.configure(scrollregion=(0, 0, total_w, 8 * track_h))

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
        self.draw_timeline()

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
        except:
            dur = 4.0
        # Generate real waveform right away
        waveform = self.compute_waveform(path) if path else []

        clip = {
            "name": name,
            "path": path,
            "start": self.playhead_time,
            "duration": dur,
            "is_piano": False,
            "waveform": waveform
        }
        self.tracks[track].append(clip)
        self.draw_timeline()
        self.status.config(text=f"Placed '{name}' on Track {track+1}")

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

    def toggle_play(self):
        if self.is_playing:
            self.pause()
        else:
            self.play()

    def play(self):
        self.is_playing = True
        # Clear any old paused state
        for ch in self.channels:
            ch.stop()
        # Reset triggered flags so everything can start fresh from this position
        for clips in self.tracks:
            for clip in clips:
                clip.pop("triggered", None)
        # Immediately start any clips that should already be playing at the current playhead
        self.start_clips_at_current_position()
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
        """Main animation / playback timing loop"""
        if self.is_playing:
            self.playhead_time += 0.03
            px = self.playhead_time * self.pixels_per_second
            self.canvas.coords(self.playhead, px, 0, px, 440)
            # Trigger clips when the playhead reaches their start
            for t_idx, clips in enumerate(self.tracks):
                if self.muted[t_idx]:
                    continue
                for clip in clips:
                    start = clip["start"]
                    # Trigger when we cross the start point
                    if (self.playhead_time >= start and
                        self.playhead_time < start + 0.1 and
                        not clip.get("triggered")):
                        clip["triggered"] = True
                        self.trigger_clip(t_idx, clip, offset_sec=0.0)
            # Reset triggered flags when looping or stopping (simplified)
        self.root.after(30, self.update_loop)

    def trigger_clip(self, track_idx, clip, offset_sec=0.0):
        """Play a clip, optionally starting from an offset (in seconds)."""
        try:
            if clip.get("is_piano"):
                note = clip["note"]
                if note in self.piano_sounds:
                    snd = self.piano_sounds[note]
                    self.channels[track_idx].play(snd)
            elif clip.get("path"):
                snd = pygame.mixer.Sound(clip["path"])
                arr = pygame.sndarray.array(snd)
                # Calculate sample offset
                start_sample = int(offset_sec * SAMPLE_RATE)
                if start_sample >= len(arr):
                    return
                # Slice the array from the offset
                sliced = arr[start_sample:]
                if len(sliced) == 0:
                    return
                # Create a new sound from the remaining audio
                partial = pygame.sndarray.make_sound(sliced)
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
        dialog.geometry("420x220")
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
        name_entry.insert(0, "My Song")
        name_entry.pack(side="left", padx=8)
        name_entry.focus()

        # Format
        fmt_frame = tk.Frame(dialog, bg="#1a1a1a")
        fmt_frame.pack(pady=10)
        tk.Label(fmt_frame, text="Format:", bg="#1a1a1a", fg="#ccc").pack(side="left", padx=(0, 10))

        format_var = tk.StringVar(value="wav")
        for fmt in ["WAV", "MP3", "M4A"]:
            tk.Radiobutton(fmt_frame, text=fmt, variable=format_var, value=fmt.lower(),
                           bg="#1a1a1a", fg="white", selectcolor="#333",
                           activebackground="#1a1a1a", activeforeground="white",
                           font=("Segoe UI", 10)).pack(side="left", padx=8)

        def do_export():
            filename = name_entry.get().strip()
            if not filename:
                messagebox.showwarning("Name needed", "Please enter a file name.", parent=dialog)
                return
            fmt = format_var.get()
            # Clean filename
            filename = "".join(c for c in filename if c.isalnum() or c in " _-")
            if not filename:
                filename = "My Song"
            full_name = f"{filename}.{fmt}"

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
        # Progress popup
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
            max_end = 10.0
            for clips in self.tracks:
                for c in clips:
                    max_end = max(max_end, c["start"] + c.get("duration", 2.0))
            total_samples = int(max_end * SAMPLE_RATE)
            # No hard 2-minute limit — export the full length
            # (very long songs may use more memory)
            mix = np.zeros((total_samples, 2), dtype=np.float32)

            status_lbl.config(text="Mixing tracks...")
            self.root.update()

            clip_count = sum(len(c) for c in self.tracks)
            done = 0

            for t_idx, clips in enumerate(self.tracks):
                if self.muted[t_idx]:
                    continue
                vol = self.volumes[t_idx]
                for clip in clips:
                    start_s = int(clip["start"] * SAMPLE_RATE)
                    if start_s >= total_samples:
                        continue

                    arr = None
                    if clip.get("is_piano") and clip.get("note") in self.piano_sounds:
                        arr = pygame.sndarray.array(self.piano_sounds[clip["note"]]).astype(np.float32) / 32767.0
                    elif clip.get("path"):
                        try:
                            snd = pygame.mixer.Sound(clip["path"])
                            arr = pygame.sndarray.array(snd).astype(np.float32) / 32767.0
                        except Exception:
                            arr = None

                    if arr is not None:
                        if arr.ndim == 1:
                            arr = np.column_stack((arr, arr))
                        end = min(start_s + len(arr), total_samples)
                        mix[start_s:end] += arr[:end - start_s] * vol

                    done += 1
                    status_lbl.config(text=f"Mixing... {done}/{clip_count}")
                    self.root.update()

            status_lbl.config(text="Normalizing & saving...")
            self.root.update()

            peak = np.max(np.abs(mix))
            if peak > 0:
                mix = mix / peak * 0.9
            mix_int = (mix * 32767).astype(np.int16)

            # Always write a real WAV first
            wav_path = path if fmt == "wav" else path.rsplit(".", 1)[0] + ".wav"
            with wave.open(wav_path, "wb") as wf:
                wf.setnchannels(2)
                wf.setsampwidth(2)
                wf.setframerate(SAMPLE_RATE)
                wf.writeframes(mix_int.tobytes())

            final_path = wav_path
            if fmt in ("mp3", "m4a"):
                import shutil
                if shutil.which("ffmpeg"):
                    status_lbl.config(text=f"Converting to {fmt.upper()}...")
                    self.root.update()
                    import subprocess
                    cmd = ["ffmpeg", "-y", "-i", wav_path, "-b:a", "192k", path]
                    result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                    if result.returncode == 0 and os.path.exists(path):
                        final_path = path
                        try:
                            os.remove(wav_path)
                        except:
                            pass
                    else:
                        messagebox.showwarning(
                            "Conversion failed",
                            f"FFmpeg was found but conversion failed.\nSaved as WAV instead:\n{wav_path}",
                            parent=progress_win
                        )
                else:
                    messagebox.showinfo(
                        "FFmpeg needed for MP3/M4A",
                        "To export as MP3 or M4A you need FFmpeg installed.\n\n"
                        "How to install:\n"
                        "• Windows: download from https://ffmpeg.org/download.html\n"
                        "  or run: winget install ffmpeg\n"
                        "• Mac: brew install ffmpeg\n"
                        "• Linux: sudo apt install ffmpeg\n\n"
                        f"For now your song was saved as WAV:\n{wav_path}",
                        parent=progress_win
                    )

            bar.stop()
            progress_win.destroy()
            messagebox.showinfo("Export Complete", f"Song saved successfully:\n{final_path}")

        except Exception as e:
            bar.stop()
            progress_win.destroy()
            messagebox.showerror("Export Error", f"Could not export:\n{str(e)}")

    def bind_keys(self):
        self.root.bind("<space>", lambda e: self.toggle_play())
        self.root.bind("<Shift-P>", lambda e: self.stop())
        self.root.bind("<Shift-p>", lambda e: self.stop())
        self.root.bind("<Delete>", self.delete_selected)
        self.root.bind("<BackSpace>", self.delete_selected)
        self.root.bind("<Control-a>", self.select_all_clips)
        self.root.bind("<Control-A>", self.select_all_clips)
        # Select track with number keys 1-8
        for i in range(8):
            self.root.bind(str(i+1), lambda e, idx=i: self.select_track(idx))

    def select_track(self, idx):
        self.selected_track = idx
        self.status.config(text=f"Selected Track {idx+1}")

def main():
    root = tk.Tk()
    # Darker ttk style
    style = ttk.Style()
    style.theme_use("clam")
    app = MusicMaker(root)
    root.mainloop()

if __name__ == "__main__":
    main()
