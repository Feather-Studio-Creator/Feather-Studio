# Feather-Studio-1.0.0
a music creator made by Feather Studio Music, or the owner of Kipdy (Kipdy Trango)
Please make sure you have python 3.13+ and NumPy installed, or it will not work
# Feather Studio

A simple, dark-themed music maker built in Python.  
Create tracks, drop in audio clips, play the piano, record notes, and export your song.

![Feather Studio](https://via.placeholder.com/800x400/1a1a1a/ffffff?text=Feather+Studio)

## Features

- Multi-track timeline (8 tracks)
- Import audio files or entire folders
- Double-click to place clips on the timeline
- Real waveforms on every audio clip
- Colored tracks with darker waveform overlays
- Click the timeline header to move the playhead
- Play / Pause / Stop with keyboard shortcuts
- Virtual piano (click to play)
- Record mode – piano notes are placed on the timeline
- Per-track volume faders and mute buttons
- Select clips (Shift+click for multi-select, Ctrl+A for all)
- Delete selected clips with Backspace or Delete
- Export to **WAV**, **MP3**, or **M4A**
- Dark FL Studio-inspired interface

## Keyboard Shortcuts

| Key          | Action              |
|--------------|---------------------|
| `Space`      | Play / Pause        |
| `Shift + P`  | Stop                |
| `1` – `8`    | Select track        |
| `Ctrl + A`   | Select all clips    |
| `Backspace` / `Delete` | Delete selected clips |
| `Shift + Click` | Multi-select clips |

## Requirements

- Python 3.13 or newer
- pygame
- numpy

Optional (for MP3 / M4A export):
- FFmpeg

## Installation

```bash
pip install pygame numpy
