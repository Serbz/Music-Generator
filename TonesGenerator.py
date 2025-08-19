# First, you'll need to install the following libraries:
# pip install pygame
# pip install scipy
# pip install midiutil

import numpy as np
import pygame
import time
import random
import tkinter as tk
from tkinter import scrolledtext, ttk, filedialog, BooleanVar
import threading
from scipy import signal
import wave
import os
import sys
from midiutil import MIDIFile
import math
import traceback
import copy
import json

class HarmonizerApp:
    def __init__(self, master, ui_mode=True):
        self.master = master
        self.ui_mode = ui_mode
        
        if self.ui_mode:
            master.title("Harmonizer (Advanced Logic)")
            master.geometry("850x800")
            pygame.mixer.init(frequency=44100, size=-16, channels=16, buffer=1024)
            master.protocol("WM_DELETE_WINDOW", self.on_closing)
            master.configure(bg='#2e2e2e')

        self.SETTINGS_FILE = "harmonizer_settings.json"
        
        self.harmonic_channel = None
        self.drum_channel = None
        
        self.lock = threading.Lock()
        self.music_thread = None
        self.stop_event = threading.Event()
        
        self.last_song_data, self.last_drum_data, self.last_master_audio, self.last_melody_bpm = None, None, None, None
        self.last_bit_depth, self.last_sample_rate = 24, 44100
        
        self.last_harmonic_sound, self.last_drum_sound = None, None
        self.thematic_seed = None

        # --- Debug Window ---
        self.debug_window = None
        self.debug_log_area = None

        # --- Parameters, constants, and helper dictionaries ---
        self.NOTE_FREQUENCIES = {
            'C': 261.63, 'C#': 277.18, 'D': 293.66, 'D#': 311.13, 'E': 329.63, 'F': 349.23,
            'F#': 369.99, 'G': 392.00, 'G#': 415.30, 'A': 440.00, 'A#': 466.16, 'B': 493.88
        }
        self.ALL_NOTES = list(self.NOTE_FREQUENCIES.keys())
        self.MAJOR_INTERVALS = [0, 2, 4, 5, 7, 9, 11] # Ionian
        self.DORIAN_INTERVALS = [0, 2, 3, 5, 7, 9, 10]
        self.PHRYGIAN_INTERVALS = [0, 1, 3, 5, 7, 8, 10]
        self.LYDIAN_INTERVALS = [0, 2, 4, 6, 7, 9, 11]
        self.MIXOLYDIAN_INTERVALS = [0, 2, 4, 5, 7, 9, 10]
        self.MINOR_INTERVALS = [0, 2, 3, 5, 7, 8, 10] # Aeolian
        self.LOCRIAN_INTERVALS = [0, 1, 3, 5, 6, 8, 10]
        self.CUSTOM_INTERVALS = [0, 2, 4, 6, 7, 9, 11]
        self.PHRYGIAN_DOMINANT_INTERVALS = [0, 1, 4, 5, 7, 8, 10]
        self.HARMONIC_MINOR_INTERVALS = [0, 2, 3, 5, 7, 8, 11]
        self.MELODIC_MINOR_INTERVALS = [0, 2, 3, 5, 7, 9, 11]
        self.PENTATONIC_MAJOR_INTERVALS = [0, 2, 4, 7, 9]
        self.PENTATONIC_MINOR_INTERVALS = [0, 3, 5, 7, 10]
        self.BLUES_INTERVALS = [0, 3, 5, 6, 7, 10]
        self.DIMINISHED_7_INTERVALS = [0, 3, 6, 9]

        # --- NEW: Modal characteristics for melodic generation ---
        self.MODAL_CHARACTERISTICS = {
            'Dorian': 6, # Major 6th
            'Phrygian': 1, # Minor 2nd
            'Lydian': 4, # Augmented 4th
            'Mixolydian': 6, # Minor 7th (index 6 in a 0-6 scale)
            'Locrian': 1, # Minor 2nd
        }
        
        # --- NEW: Helper set for robust fallback logic ---
        self.MINOR_LIKE_SCALES = {'Minor', 'Dorian', 'Phrygian', 'Locrian', 'Harmonic Minor', 'Melodic Minor', 'Pentatonic Minor', 'Blues'}


        # --- NEW: Rhythmic motifs for more structured rhythm ---
        self.RHYTHMIC_MOTIFS = {
            'straight': [1, 1, 1, 1],
            'syncopated': [0.75, 0.75, 0.5, 1, 1],
            'offbeat': [0.5, 1, 0.5, 1, 0.5, 0.5],
            'dotted': [1.5, 0.5, 1.5, 0.5],
            'gallop': [0.75, 0.25, 1, 0.75, 0.25, 1],
        }

        self.WAVEFORM_DYNAMICS = {
            'Sine': 1.0, 'Triangle': 0.9, 'Square': 0.6, 'Sawtooth': 0.7, 'Rich Saw': 0.65,
            'Piano': 0.9, 'Karplus-Strong': 0.95, 'FM E-Piano': 0.85, 'Synth Pad': 0.8,
            'Drawbar Organ': 0.75, 'Hollow Square': 0.8, 'Pluck Synth': 0.9, 'Brass Ensemble': 0.8
        }

        self.CLASSICAL_SCHEMAS = {
            'Prinner': {'pattern': [0, -1, -2, -3, -4, 2, 0], 'durations': [1, 0.5, 0.5, 0.5, 0.5, 1, 1]},
            'Meyer': {'pattern': [0, -1, 0, 4, 2, 0], 'durations': [1, 1, 1, 1, 1, 1]},
            'Galant': {'pattern': [0, 1, 2, 0], 'durations': [0.5, 0.5, 0.5, 0.5]}
        }
        
        self.MODAL_INTERCHANGE_MAP = {
            'Major': {'ii': 'ii°', 'iii': 'III', 'IV': 'iv', 'vi': 'VI'},
            'Minor': {'iv': 'IV', 'v': 'V', 'VII': 'vii°'}
        }


        self.POETIC_METERS = {
            'Iambic': [0.5, 1.0], 'Trochaic': [1.0, 0.5], 'Anapestic': [0.5, 0.5, 1.0],
            'Dactylic': [1.0, 0.5, 0.5], 'Spondaic': [1.0, 1.0], 'Pyrrhic': [0.5, 0.5]
        }

        self.MUSICAL_SCALES = {}
        for note, base_freq in self.NOTE_FREQUENCIES.items():
            self.MUSICAL_SCALES[f"{note} Major"] = [base_freq * (2**(interval/12)) for interval in self.MAJOR_INTERVALS]
            self.MUSICAL_SCALES[f"{note} Dorian"] = [base_freq * (2**(interval/12)) for interval in self.DORIAN_INTERVALS]
            self.MUSICAL_SCALES[f"{note} Phrygian"] = [base_freq * (2**(interval/12)) for interval in self.PHRYGIAN_INTERVALS]
            self.MUSICAL_SCALES[f"{note} Lydian"] = [base_freq * (2**(interval/12)) for interval in self.LYDIAN_INTERVALS]
            self.MUSICAL_SCALES[f"{note} Mixolydian"] = [base_freq * (2**(interval/12)) for interval in self.MIXOLYDIAN_INTERVALS]
            self.MUSICAL_SCALES[f"{note} Minor"] = [base_freq * (2**(interval/12)) for interval in self.MINOR_INTERVALS]
            self.MUSICAL_SCALES[f"{note} Locrian"] = [base_freq * (2**(interval/12)) for interval in self.LOCRIAN_INTERVALS]
            self.MUSICAL_SCALES[f"{note} Custom"] = [base_freq * (2**(interval/12)) for interval in self.CUSTOM_INTERVALS]
            self.MUSICAL_SCALES[f"{note} Phrygian Dominant"] = [base_freq * (2**(interval/12)) for interval in self.PHRYGIAN_DOMINANT_INTERVALS]
            self.MUSICAL_SCALES[f"{note} Harmonic Minor"] = [base_freq * (2**(interval/12)) for interval in self.HARMONIC_MINOR_INTERVALS]
            self.MUSICAL_SCALES[f"{note} Melodic Minor"] = [base_freq * (2**(interval/12)) for interval in self.MELODIC_MINOR_INTERVALS]
            self.MUSICAL_SCALES[f"{note} Pentatonic Major"] = [base_freq * (2**(interval/12)) for interval in self.PENTATONIC_MAJOR_INTERVALS]
            self.MUSICAL_SCALES[f"{note} Pentatonic Minor"] = [base_freq * (2**(interval/12)) for interval in self.PENTATONIC_MINOR_INTERVALS]
            self.MUSICAL_SCALES[f"{note} Blues"] = [base_freq * (2**(interval/12)) for interval in self.BLUES_INTERVALS]

        self.DIATONIC_CHORDS = {
            'Major': {'I': [0, 2, 4], 'ii': [1, 3, 5], 'iii': [2, 4, 6], 'IV': [3, 5, 7], 'V': [4, 6, 8], 'vi': [5, 7, 9], 'vii°': [6, 8, 10]},
            'Dorian': {'i': [0, 2, 4], 'ii': [1, 3, 5], 'III': [2, 4, 6], 'IV': [3, 5, 7], 'v': [4, 6, 8], 'vi°': [5, 7, 9], 'VII': [6, 8, 10]},
            'Phrygian': {'i': [0, 2, 4], 'II': [1, 3, 5], 'III': [2, 4, 6], 'iv': [3, 5, 7], 'v°': [4, 6, 8], 'VI': [5, 7, 9], 'vii': [6, 8, 10]},
            'Lydian': {'I': [0, 2, 4], 'II': [1, 3, 5], 'iii': [2, 4, 6], '#iv°': [3, 5, 7], 'V': [4, 6, 8], 'vi': [5, 7, 9], 'vii': [6, 8, 10]},
            'Mixolydian': {'I': [0, 2, 4], 'ii': [1, 3, 5], 'iii°': [2, 4, 6], 'IV': [3, 5, 7], 'v': [4, 6, 8], 'vi': [5, 7, 9], 'VII': [6, 8, 10]},
            'Minor': {'i': [0, 2, 4], 'ii°': [1, 3, 5], 'III': [2, 4, 6], 'iv': [3, 5, 7], 'v': [4, 6, 8], 'VI': [5, 7, 9], 'VII': [6, 8, 10]},
            'Locrian': {'i°': [0, 2, 4], 'II': [1, 3, 5], 'iii': [2, 4, 6], 'iv': [3, 5, 7], 'V': [4, 6, 8], 'VI': [5, 7, 9], 'vii': [6, 8, 10]},
            'Custom': {'i': [0, 2, 4], 'II': [1, 3, 5], 'iii': [2, 4, 6], 'IV+': [3, 5, 7], 'V': [4, 6, 8], 'vi': [5, 7, 9], 'vii': [6, 8, 10]},
            'Phrygian Dominant': {'i': [0, 2, 4], 'II': [1, 3, 5], 'iii': [2, 4, 6], 'iv': [3, 5, 7], 'V': [4, 6, 8], 'VI': [5, 7, 9], 'vii': [6, 8, 10]},
            'Harmonic Minor': {'i': [0, 2, 4], 'ii°': [1, 3, 5], 'III+': [2, 4, 6], 'iv': [3, 5, 7], 'V': [4, 6, 8], 'VI': [5, 7, 9], 'vii°': [6, 8, 10]},
            'Melodic Minor': {'i': [0, 2, 4], 'ii': [1, 3, 5], 'III+': [2, 4, 6], 'IV': [3, 5, 7], 'V': [4, 6, 8], 'vi°': [5, 7, 9], 'vii°': [6, 8, 10]},
            'Pentatonic Major': {'I': [0, 2, 4], 'ii': [1, 3, 5], 'vi': [2, 4, 6]},
            'Pentatonic Minor': {'i': [0, 2, 4], 'IV': [1, 3, 5], 'v': [2, 4, 6]},
            'Blues': {'i': [0, 1, 4], 'iv': [1, 3, 5], 'v': [2, 4, 0]} 
        }
        
        # --- FIXED: Added comprehensive progressions for all modes ---
        self.CHORD_PROGRESSIONS = {
            'Major': {'intro': ['I', 'IV'], 'verse': ['I', 'vi', 'IV', 'V'], 'pre-chorus': ['ii', 'IV', 'V'], 'chorus': ['I', 'V', 'vi', 'IV'], 'bridge': ['vi', 'V', 'IV', 'IV'], 'solo': ['I', 'V', 'vi', 'IV'], 'outro': ['IV', 'V', 'I'], 'development': ['ii', 'V', 'I', 'vi'], 'pachelbel': ['I', 'V', 'vi', 'iii', 'IV', 'I', 'IV', 'V'], '50s': ['I', 'vi', 'IV', 'V']},
            'Dorian': {'intro': ['i', 'IV'], 'verse': ['i', 'IV', 'i', 'VII'], 'chorus': ['i', 'IV', 'VII', 'IV'], 'bridge': ['IV', 'VII', 'i', 'i'], 'solo': ['i', 'IV', 'i', 'IV'], 'outro': ['IV', 'i']},
            'Phrygian': {'intro': ['i', 'II'], 'verse': ['i', 'VI', 'i', 'II'], 'chorus': ['i', 'II', 'VI', 'II'], 'bridge': ['VI', 'vii', 'i', 'i'], 'solo': ['i', 'II', 'i', 'II'], 'outro': ['II', 'i']},
            'Lydian': {'intro': ['I', 'II'], 'verse': ['I', 'V', 'I', 'II'], 'chorus': ['I', 'II', 'V', 'II'], 'bridge': ['vi', 'V', 'II', 'II'], 'solo': ['I', 'II', 'I', 'II'], 'outro': ['II', 'V', 'I']},
            'Mixolydian': {'intro': ['I', 'VII'], 'verse': ['I', 'VII', 'IV', 'I'], 'chorus': ['I', 'v', 'IV', 'I'], 'bridge': ['IV', 'v', 'I', 'I'], 'solo': ['I', 'VII', 'IV', 'VII'], 'outro': ['VII', 'IV', 'I']},
            'Minor': {'intro': ['i', 'VI'], 'verse': ['i', 'VI', 'iv', 'v'], 'pre-chorus': ['ii°', 'VI', 'v'], 'chorus': ['i', 'v', 'VI', 'iv'], 'bridge': ['VI', 'VII', 'i', 'i'], 'solo': ['i', 'v', 'VI', 'iv'], 'outro': ['iv', 'v', 'i'], 'development': ['ii°', 'v', 'i', 'VI'], 'lament_bridge': ['i', 'VII', 'VI', 'V']},
            'Locrian': {'intro': ['i°', 'iv'], 'verse': ['i°', 'VI', 'iv', 'v°'], 'chorus': ['i°', 'iv', 'V', 'i°'], 'bridge': ['VI', 'V', 'iv', 'iv'], 'solo': ['i°', 'iv', 'i°', 'iv'], 'outro': ['iv', 'V', 'i°']},
            'Custom': {'intro': ['i', 'IV+'], 'verse': ['i', 'vi', 'ii', 'V'], 'pre-chorus': ['II', 'V'], 'chorus': ['i', 'V', 'vi', 'IV+'], 'bridge': ['vi', 'V', 'IV+', 'IV+'], 'solo': ['i', 'V', 'vi', 'IV+'], 'outro': ['II', 'V', 'i'], 'development': ['ii', 'V', 'i', 'vi']},
            'Phrygian Dominant': {'intro': ['i', 'VI'], 'verse': ['i', 'II', 'VI', 'V'], 'pre-chorus': ['iv', 'V'], 'chorus': ['i', 'VI', 'V', 'i'], 'bridge': ['II', 'V', 'i', 'i'], 'solo': ['i', 'VI', 'V', 'i'], 'outro': ['II', 'V', 'i'], 'development': ['iv', 'V', 'i', 'II']},
            'Harmonic Minor': {'intro': ['i', 'iv'], 'verse': ['i', 'V', 'i', 'VI'], 'pre-chorus': ['ii°', 'V'], 'chorus': ['i', 'VI', 'V'], 'bridge': ['VI', 'V', 'III+'], 'solo': ['i', 'VI', 'V'], 'outro': ['iv', 'v', 'i'], 'development': ['ii°', 'V', 'VI', 'III+']},
            'Melodic Minor': {'intro': ['i', 'IV'], 'verse': ['i', 'V', 'i', 'vi°'], 'pre-chorus': ['IV', 'V'], 'chorus': ['i', 'vi°', 'V'], 'bridge': ['IV', 'V', 'III+'], 'solo': ['i', 'vi°', 'V'], 'outro': ['IV', 'V', 'i'], 'development': ['ii', 'V', 'IV', 'III+']},
            'Pentatonic Major': {'intro': ['I'], 'verse': ['I', 'vi', 'I'], 'pre-chorus': ['ii'], 'chorus': ['I', 'vi', 'ii'], 'bridge': ['vi', 'ii', 'I'], 'solo': ['I', 'vi', 'ii'], 'outro': ['ii', 'I'], 'development': ['vi', 'ii']},
            'Pentatonic Minor': {'intro': ['i'], 'verse': ['i', 'v', 'i'], 'pre-chorus': ['IV'], 'chorus': ['i', 'v', 'IV'], 'bridge': ['v', 'IV', 'i'], 'solo': ['i', 'v', 'IV'], 'outro': ['v', 'i'], 'development': ['v', 'IV']},
            'Blues': {'intro': ['i'], 'verse': ['i', 'i', 'i', 'i', 'iv', 'iv', 'i', 'i', 'v', 'iv', 'i', 'i'], 'chorus': ['i', 'iv', 'v'], 'bridge': ['iv', 'iv', 'i', 'i'], 'solo': ['i', 'i', 'i', 'i', 'iv', 'iv', 'i', 'i', 'v', 'iv', 'i', 'i'], 'outro': ['v', 'i']}
        }

        self.DRUM_SOUND_PROPERTIES = {
            'kick': {'midi_note': 36}, 'snare': {'midi_note': 38}, 'hihat_closed': {'midi_note': 42},
            'hihat_open': {'midi_note': 46}, 'tom': {'midi_note': 45}, 'crash': {'midi_note': 49}
        }
        
        self.DRUM_PATTERNS = {
            'rock': {
                'main': [ (0, 'kick'), (0.5, 'hihat_closed'), (1, 'snare'), (1.5, 'hihat_closed'), (2, 'kick'), (2.5, 'hihat_closed'), (3, 'snare'), (3.5, 'hihat_closed') ],
                'fill': [ (0, 'snare'), (0.5, 'snare'), (1, 'tom'), (1.5, 'tom'), (2, 'snare'), (2.5, 'tom'), (3, 'tom'), (3.5, 'crash') ]
            },
            'hiphop': {
                'main': [ (0, 'kick'), (1, 'snare'), (2, 'kick'), (2.5, 'kick'), (3, 'snare') ],
                'fill': [ (3, 'snare'), (3.25, 'snare'), (3.5, 'snare'), (3.75, 'snare') ]
            },
            'dance': {
                'main': [ (0, 'kick'), (0.5, 'hihat_open'), (1, 'kick'), (1.5, 'hihat_open'), (2, 'kick'), (2.5, 'hihat_open'), (3, 'kick'), (3.5, 'hihat_open') ],
                'fill': [ (3, 'snare'), (3.25, 'snare'), (3.5, 'snare'), (3.75, 'crash') ]
            }
        }
        
        self.DRUM_MIX_VOLUMES = {
            'kick': 1.2, 'snare': 1.0, 'tom': 0.9,
            'hihat_closed': 0.7, 'hihat_open': 0.7, 'crash': 0.65
        }
        # --- End of constants section ---

        if self.ui_mode:
            self._setup_ui()
        else:
            self.settings = {}

        self.scale_types = sorted(list(set([k.split(' ', 1)[1] for k in self.MUSICAL_SCALES.keys()])))
        if self.ui_mode:
            self.scale_vars = {st: BooleanVar(value=True) for st in self.scale_types}
        else:
            self.scale_vars = {} # Will be a simple dict in no-ui mode
        
        self._load_settings()

        if self.ui_mode:
            self.entry_duration.bind("<KeyRelease>", self._save_settings)
            self.bit_depth_var.trace("w", self._save_settings)

    def _setup_ui(self):
        style = ttk.Style(); style.theme_use('clam'); style.configure("TScale", background="#2e2e2e", troughcolor="#444444")
        frame = tk.Frame(self.master, padx=10, pady=10, bg='#2e2e2e'); frame.pack(fill=tk.BOTH, expand=True)

        # --- Top Row: Playback Controls & Main Options ---
        top_frame = tk.Frame(frame, bg='#2e2e2e'); top_frame.pack(pady=5, fill=tk.X)
        
        # Playback Controls
        self.play_button = tk.Button(top_frame, text="Play", command=self.start_music, bg='#555555', fg='white'); self.play_button.pack(side=tk.LEFT, padx=5)
        self.replay_button = tk.Button(top_frame, text="Replay", command=self.replay_music, bg='#555555', fg='white', state=tk.DISABLED); self.replay_button.pack(side=tk.LEFT, padx=5)
        self.stop_button = tk.Button(top_frame, text="Stop", command=self.stop_music, bg='#555555', fg='white', state=tk.DISABLED); self.stop_button.pack(side=tk.LEFT, padx=5)
        self.loop_var = BooleanVar(); self.loop_check = tk.Checkbutton(top_frame, text="Loop", variable=self.loop_var, bg='#2e2e2e', fg='white', selectcolor='#444444', command=self._save_settings); self.loop_check.pack(side=tk.LEFT, padx=10)
        self.scales_button = tk.Button(top_frame, text="Scales", command=self._open_scales_window, bg='#4d6b88', fg='white'); self.scales_button.pack(side=tk.LEFT, padx=5)

        # Duration, Bit Depth, Debug
        tk.Label(top_frame, text="Duration (s):", bg='#2e2e2e', fg='white').pack(side=tk.LEFT, padx=(20, 5))
        self.entry_duration = tk.Entry(top_frame, bg='#444444', fg='white', width=10); self.entry_duration.pack(side=tk.LEFT, padx=5)
        
        self.debug_button = tk.Button(top_frame, text="Debug", command=self.open_debug_window, bg='#4d6b88', fg='white'); self.debug_button.pack(side=tk.RIGHT, padx=5)

        # --- Centered Waveform Options ---
        waveform_frame = tk.Frame(frame, bg='#2e2e2e'); waveform_frame.pack(pady=10)
        waveforms = ["Sine", "Square", "Sawtooth", "Triangle", "Piano", "Karplus-Strong", 
                     "Rich Saw", "FM E-Piano", "Synth Pad", "Drawbar Organ", "Hollow Square",
                     "Pluck Synth", "Brass Ensemble", "Random"]
        
        self.auto_wave_var = BooleanVar(value=True)
        self.auto_wave_check = tk.Checkbutton(waveform_frame, text="Auto-Select Waveforms", variable=self.auto_wave_var, bg='#2e2e2e', fg='white', selectcolor='#444444', command=self._save_settings)
        self.auto_wave_check.pack(side=tk.LEFT, padx=(5, 15))

        self.melody1_waveform_var = tk.StringVar(self.master)
        tk.Label(waveform_frame, text="Melody 1:", bg='#2e2e2e', fg='white').pack(side=tk.LEFT, padx=5)
        self.m1_waveform_menu = tk.OptionMenu(waveform_frame, self.melody1_waveform_var, *waveforms, command=self._save_settings); self.m1_waveform_menu.pack(side=tk.LEFT, padx=5)

        self.melody2_waveform_var = tk.StringVar(self.master)
        tk.Label(waveform_frame, text="Melody 2:", bg='#2e2e2e', fg='white').pack(side=tk.LEFT, padx=5)
        self.m2_waveform_menu = tk.OptionMenu(waveform_frame, self.melody2_waveform_var, *waveforms, command=self._save_settings); self.m2_waveform_menu.pack(side=tk.LEFT, padx=5)
        
        self.chord_waveform_var = tk.StringVar(self.master)
        tk.Label(waveform_frame, text="Chords:", bg='#2e2e2e', fg='white').pack(side=tk.LEFT, padx=5)
        self.chord_waveform_menu = tk.OptionMenu(waveform_frame, self.chord_waveform_var, *waveforms, command=self._save_settings); self.chord_waveform_menu.pack(side=tk.LEFT, padx=5)

        self.bass_waveform_var = tk.StringVar(self.master)
        tk.Label(waveform_frame, text="Bass:", bg='#2e2e2e', fg='white').pack(side=tk.LEFT, padx=5)
        self.bass_waveform_menu = tk.OptionMenu(waveform_frame, self.bass_waveform_var, *waveforms, command=self._save_settings); self.bass_waveform_menu.pack(side=tk.LEFT, padx=5)

        # --- Volume Sliders ---
        volume_frame = tk.Frame(frame, bg='#2e2e2e'); volume_frame.pack(pady=5, fill=tk.X)
        tk.Label(volume_frame, text="Harmonic Vol:", bg='#2e2e2e', fg='white').pack(side=tk.LEFT, padx=5)
        self.melody_volume_slider = ttk.Scale(volume_frame, from_=0, to=100, orient=tk.HORIZONTAL, command=self._update_and_save_melody_volume); self.melody_volume_slider.pack(side=tk.LEFT, fill=tk.X, expand=True)
        tk.Label(volume_frame, text="Drum Volume:", bg='#2e2e2e', fg='white').pack(side=tk.LEFT, padx=5)
        self.drum_volume_slider = ttk.Scale(volume_frame, from_=0, to=100, orient=tk.HORIZONTAL, command=self._update_and_save_drum_volume); self.drum_volume_slider.pack(side=tk.LEFT, fill=tk.X, expand=True)

        # --- Log Areas ---
        main_log_frame = tk.Frame(frame, bg='#2e2e2e'); main_log_frame.pack(pady=5, fill=tk.X)
        tk.Label(main_log_frame, text="Main Events Log", bg='#2e2e2e', fg='white').pack()
        self.main_log_area = scrolledtext.ScrolledText(main_log_frame, wrap=tk.WORD, height=6, state='disabled', bg='black', fg='white'); self.main_log_area.pack(fill=tk.X)
        self.main_log_area.tag_config('main', foreground='lightblue')
        
        # Grid for logs and export buttons
        grid_frame = tk.Frame(frame, bg='#2e2e2e'); grid_frame.pack(pady=5, fill=tk.BOTH, expand=True)
        grid_frame.grid_columnconfigure(0, weight=1); grid_frame.grid_columnconfigure(1, weight=1)
        grid_frame.grid_rowconfigure(0, weight=1); grid_frame.grid_rowconfigure(1, weight=1)
        grid_frame.grid_rowconfigure(2, weight=1)

        # Melody 1 Log
        melody1_log_frame = tk.Frame(grid_frame, bg='#2e2e2e'); melody1_log_frame.grid(row=0, column=0, sticky='nsew', padx=2, pady=2)
        tk.Label(melody1_log_frame, text="Melody 1 Log", bg='#2e2e2e', fg='white').pack()
        self.melody1_log_area = scrolledtext.ScrolledText(melody1_log_frame, wrap=tk.WORD, height=5, state='disabled', bg='black', fg='lightgreen'); self.melody1_log_area.pack(fill=tk.BOTH, expand=True)
        self.melody1_log_area.tag_config('melody1', foreground='lightgreen')

        # Bass Log
        bass_log_frame = tk.Frame(grid_frame, bg='#2e2e2e'); bass_log_frame.grid(row=0, column=1, sticky='nsew', padx=2, pady=2)
        tk.Label(bass_log_frame, text="Bass Log", bg='#2e2e2e', fg='white').pack()
        self.bass_log_area = scrolledtext.ScrolledText(bass_log_frame, wrap=tk.WORD, height=5, state='disabled', bg='black', fg='#FFC0CB'); self.bass_log_area.pack(fill=tk.BOTH, expand=True)
        self.bass_log_area.tag_config('bass', foreground='#FFC0CB')

        # Melody 2 Log
        melody2_log_frame = tk.Frame(grid_frame, bg='#2e2e2e'); melody2_log_frame.grid(row=1, column=0, sticky='nsew', padx=2, pady=2)
        tk.Label(melody2_log_frame, text="Melody 2 Log", bg='#2e2e2e', fg='white').pack()
        self.melody2_log_area = scrolledtext.ScrolledText(melody2_log_frame, wrap=tk.WORD, height=5, state='disabled', bg='black', fg='#98FB98'); self.melody2_log_area.pack(fill=tk.BOTH, expand=True)
        self.melody2_log_area.tag_config('melody2', foreground='#98FB98')

        # Chord Log
        chord_log_frame = tk.Frame(grid_frame, bg='#2e2e2e'); chord_log_frame.grid(row=1, column=1, sticky='nsew', padx=2, pady=2)
        tk.Label(chord_log_frame, text="Chord Log", bg='#2e2e2e', fg='white').pack()
        self.chord_log_area = scrolledtext.ScrolledText(chord_log_frame, wrap=tk.WORD, height=5, state='disabled', bg='black', fg='#ADD8E6'); self.chord_log_area.pack(fill=tk.BOTH, expand=True)
        self.chord_log_area.tag_config('chords', foreground='#ADD8E6')
        
        # Drum Log
        drum_log_frame = tk.Frame(grid_frame, bg='#2e2e2e'); drum_log_frame.grid(row=2, column=0, sticky='nsew', padx=2, pady=2)
        tk.Label(drum_log_frame, text="Drum Events Log", bg='#2e2e2e', fg='white').pack()
        self.drum_log_area = scrolledtext.ScrolledText(drum_log_frame, wrap=tk.WORD, height=5, state='disabled', bg='black', fg='orange'); self.drum_log_area.pack(fill=tk.BOTH, expand=True)
        self.drum_log_area.tag_config('drums', foreground='orange')

        # --- Export and Reload Buttons Frame ---
        export_reload_frame = tk.Frame(grid_frame, bg='#2e2e2e'); export_reload_frame.grid(row=2, column=1, sticky='nsew', padx=2, pady=2)
        export_reload_frame.grid_rowconfigure(0, weight=1)
        export_reload_frame.grid_columnconfigure(0, weight=1)

        button_container = tk.Frame(export_reload_frame, bg='#2e2e2e')
        button_container.pack(anchor='center', expand=True)

        # New top row for WAV export and Bit Depth
        export_top_row = tk.Frame(button_container, bg='#2e2e2e')
        export_top_row.pack(pady=5)
        
        self.export_wav_button = tk.Button(export_top_row, text="Export WAV", command=self.export_wav_file, bg='#555555', fg='white', state=tk.DISABLED)
        self.export_wav_button.pack(side=tk.LEFT, padx=5)

        self.bit_depth_var = tk.StringVar(self.master)
        self.bit_depth_var.set("24")
        tk.Label(export_top_row, text="Bit Depth:", bg='#2e2e2e', fg='white').pack(side=tk.LEFT, padx=(10, 2))
        self.bit_depth_menu = tk.OptionMenu(export_top_row, self.bit_depth_var, "16", "24", command=self._save_settings)
        self.bit_depth_menu.pack(side=tk.LEFT, padx=2)
        
        # MIDI button on its own row, centered under the frame above
        self.export_midi_button = tk.Button(button_container, text="Export MIDI", command=self.export_midi_file, bg='#555555', fg='white', state=tk.DISABLED)
        self.export_midi_button.pack(pady=5)

        self.reload_button = tk.Button(export_reload_frame, text="Reload Script", command=self.reload_script, bg='#884d4d', fg='white'); self.reload_button.pack(side=tk.BOTTOM, anchor='se', padx=5, pady=5)


    def _save_settings(self, *args):
        settings = {
            "duration": self.entry_duration.get(),
            "bit_depth": self.bit_depth_var.get(),
            "auto_wave": self.auto_wave_var.get(),
            "m1_waveform": self.melody1_waveform_var.get(),
            "m2_waveform": self.melody2_waveform_var.get(),
            "chord_waveform": self.chord_waveform_var.get(),
            "bass_waveform": self.bass_waveform_var.get(),
            "loop": self.loop_var.get(),
            "harmonic_vol": self.melody_volume_slider.get(),
            "drum_vol": self.drum_volume_slider.get(),
            "scales": {st: var.get() for st, var in self.scale_vars.items()}
        }
        try:
            with open(self.SETTINGS_FILE, 'w') as f:
                json.dump(settings, f, indent=4)
        except Exception as e:
            self.update_log(f"Error saving settings: {e}", 'main')

    def _load_settings(self):
        try:
            if os.path.exists(self.SETTINGS_FILE):
                with open(self.SETTINGS_FILE, 'r') as f:
                    settings = json.load(f)
            else:
                settings = {} # Use defaults if file doesn't exist

            if self.ui_mode:
                self.entry_duration.delete(0, tk.END)
                self.entry_duration.insert(0, settings.get("duration", "60"))
                self.bit_depth_var.set(settings.get("bit_depth", "24"))
                self.auto_wave_var.set(settings.get("auto_wave", True))
                self.melody1_waveform_var.set(settings.get("m1_waveform", "Piano"))
                self.melody2_waveform_var.set(settings.get("m2_waveform", "Sine"))
                self.chord_waveform_var.set(settings.get("chord_waveform", "Synth Pad"))
                self.bass_waveform_var.set(settings.get("bass_waveform", "Square"))
                self.loop_var.set(settings.get("loop", False))
                self.melody_volume_slider.set(settings.get("harmonic_vol", 70.0))
                self.drum_volume_slider.set(settings.get("drum_vol", 70.0))
            else:
                self.settings = {
                    "duration": settings.get("duration", "90"),
                    "bit_depth": settings.get("bit_depth", "24"),
                    "m1_waveform": settings.get("m1_waveform", "Piano"),
                    "m2_waveform": settings.get("m2_waveform", "Sine"),
                    "chord_waveform": settings.get("chord_waveform", "Synth Pad"),
                    "bass_waveform": settings.get("bass_waveform", "Square"),
                }
            
            loaded_scales = settings.get("scales", {})
            if self.ui_mode:
                for st, var in self.scale_vars.items():
                    var.set(loaded_scales.get(st, True))
            else:
                self.scale_vars = {st: loaded_scales.get(st, True) for st in self.scale_types}
                self.settings["scales"] = self.scale_vars

        except Exception as e:
            self.update_log(f"Error loading settings: {e}", 'main')

    def _open_scales_window(self):
        scales_win = tk.Toplevel(self.master)
        scales_win.title("Enabled Scales")
        scales_win.configure(bg='#2e2e2e')
        
        main_frame = tk.Frame(scales_win, padx=10, pady=10, bg='#2e2e2e')
        main_frame.pack()

        num_scales = len(self.scale_types)
        num_cols = 2
        
        for i, scale_type in enumerate(self.scale_types):
            var = self.scale_vars[scale_type]
            row = i % ( (num_scales + 1) // num_cols )
            col = i // ( (num_scales + 1) // num_cols )
            cb = tk.Checkbutton(main_frame, text=scale_type, variable=var, bg='#2e2e2e', fg='white', selectcolor='#444444', command=self._save_settings)
            cb.grid(row=row, column=col, sticky='w', padx=5, pady=2)

    def open_debug_window(self):
        if self.debug_window is None or not self.debug_window.winfo_exists():
            self.debug_window = tk.Toplevel(self.master)
            self.debug_window.title("Debug Log")
            self.debug_window.geometry("800x600")
            self.debug_log_area = scrolledtext.ScrolledText(self.debug_window, wrap=tk.WORD, state='disabled', bg='black', fg='white')
            self.debug_log_area.pack(fill=tk.BOTH, expand=True)
            self.debug_window.protocol("WM_DELETE_WINDOW", self.on_debug_close)
            self.update_log("Debug window opened.", 'debug', debug_only=True)

    def on_debug_close(self):
        self.debug_window.destroy()
        self.debug_window = None
        self.debug_log_area = None

    def _get_related_key(self, base_key_name, relation='dominant'):
        base_note, scale_kind = base_key_name.split(' ', 1)
        base_note_index = self.ALL_NOTES.index(base_note)
        
        relations = {
            'dominant': 7,
            'subdominant': 5,
            'relative_major': 3,
            'relative_minor': -3,
            'chromatic_mediant_up': 4,
            'chromatic_mediant_down': -4,
            'tritone': 6
        }
        
        if relation in relations:
            related_index = (base_note_index + relations[relation]) % 12
            new_kind = scale_kind
            if 'relative' in relation:
                new_kind = 'Major' if 'Minor' in scale_kind else 'Minor'
            return f"{self.ALL_NOTES[related_index]} {new_kind}"

        # Fallback for original logic if needed
        return f"{self.ALL_NOTES[(base_note_index + 7) % 12]} {scale_kind}"


    def _get_contrapuntal_motion(self, m1_direction):
        if m1_direction == 0:
            return 'oblique'
        
        motions = ['similar', 'contrary', 'oblique']
        weights = [0.4, 0.5, 0.1] # Prioritize contrary motion
        return random.choices(motions, weights)[0]

    def _find_closest_note_name(self, freq):
        min_dist = float('inf')
        closest_name = "N/A"
        for note_name, base_freq in self.NOTE_FREQUENCIES.items():
            for octave in range(2, 7):
                note_freq_in_octave = base_freq * (2**(octave-4))
                if abs(freq - note_freq_in_octave) < min_dist:
                    min_dist = abs(freq - note_freq_in_octave)
                    closest_name = f"{note_name}{octave}"
        return closest_name
    
    # --- REFINED: Melodic note generation with more musical rules ---
    def _generate_melodic_note(self, current_note_index, last_note_index, last_last_note_idx, scale_notes, current_chord_indices, last_direction, consecutive_steps, section_type, scale_type, log_callback, contour, phrase_progress, motion_type=None, counter_melody_direction=None, octave_center_idx=None, is_strong_beat=False, force_leap=False, target_note_idx=None, characteristic_note_idx=None):
        scale_length = len(scale_notes)
        base_scale_len = 7 if 'Pentatonic' not in scale_type else 5
        next_note_index = current_note_index
        next_direction = last_direction
        consecutive_steps_new = consecutive_steps
        rule_applied = "No rule"

        # Apply melodic contour bias
        contour_bias = 0
        if contour == 'rising': contour_bias = 1
        elif contour == 'falling': contour_bias = -1
        elif contour == 'arch': contour_bias = 1 if phrase_progress < 0.5 else -1
        
        # Schenkerian-inspired pull towards a structural note
        if target_note_idx is not None and random.random() < 0.6:
            direction_to_target = np.sign(target_note_idx - current_note_index)
            if direction_to_target != 0:
                next_direction = direction_to_target
                next_note_index = current_note_index + next_direction
                rule_applied = "Structural Pull"
                consecutive_steps_new = 1

        # NEW: Modal characteristic note pull
        if characteristic_note_idx is not None and random.random() < 0.4:
            # Move towards the octave of the characteristic note closest to the current note
            octave_multiple = round((current_note_index - characteristic_note_idx) / base_scale_len)
            target_char_note = characteristic_note_idx + (octave_multiple * base_scale_len)
            direction_to_target = np.sign(target_char_note - current_note_index)
            if direction_to_target != 0:
                next_direction = direction_to_target
                next_note_index = current_note_index + next_direction
                rule_applied = "Modal Characteristic Pull"
        
        if force_leap:
            jump = random.choice([-7, -5, 5, 7, 9, -9]) # Wider leaps for fission
            next_note_index, next_direction, consecutive_steps_new = (current_note_index + jump), np.sign(jump), 0
            rule_applied = "Forced Leap (Fission)"
        
        if rule_applied == "No rule" and motion_type and counter_melody_direction is not None:
            if motion_type == 'contrary' and counter_melody_direction != 0:
                next_direction = -counter_melody_direction; next_note_index = (current_note_index + next_direction); rule_applied = "Contrary Motion"
            elif motion_type == 'oblique':
                next_direction = 0; next_note_index = current_note_index; rule_applied = "Oblique Motion"
            elif motion_type == 'similar' and counter_melody_direction != 0:
                next_direction = counter_melody_direction; next_note_index = (current_note_index + next_direction); rule_applied = "Similar Motion"
        
        # NEW: Guide tone bias (towards the 3rd of the chord)
        if rule_applied == "No rule" and is_strong_beat and random.random() < 0.9:
            if current_chord_indices and len(current_chord_indices) >= 2:
                # Target the third of the chord
                target_guide_tone = current_chord_indices[1] 
                octave_multiple = round((current_note_index - target_guide_tone) / base_scale_len)
                closest_guide_tone = target_guide_tone + (octave_multiple * base_scale_len)
                next_note_index = closest_guide_tone
                rule_applied = "Guide Tone (3rd)"

        if rule_applied == "No rule" and last_note_index is not None and abs(current_note_index - last_note_index) > 4: # Increased threshold for leap
            if random.random() < 0.95: # Higher chance of recovery
                next_direction = -np.sign(current_note_index - last_note_index)
                next_note_index = current_note_index + next_direction 
                consecutive_steps_new = 1
                rule_applied = "Leap Recovery (Gap Fill)"


        if rule_applied == "No rule" and consecutive_steps >= 4:
            next_direction = -last_direction if last_direction != 0 else random.choice([-1, 1]); next_note_index = (current_note_index + next_direction); consecutive_steps_new = 1; rule_applied = "Step Sequence Break"
            
        if rule_applied == "No rule":
            is_chord_tone = (current_note_index % base_scale_len) in [idx % base_scale_len for idx in current_chord_indices]
            if not is_chord_tone and random.random() < 0.9: # Increased probability
                next_direction = random.choice([-1, 1]); next_note_index = current_note_index + next_direction; consecutive_steps_new = 1; rule_applied = "Non-Chord Tone Resolution"
            else:
                if random.random() < 0.7:
                    if random.random() < 0.7 and last_direction is not None and consecutive_steps < 4:
                        next_direction, consecutive_steps_new = last_direction, consecutive_steps + 1
                    else:
                        choices = [-1, 1]
                        if contour_bias != 0: choices.extend([contour_bias] * 2) # Add weight to contour direction
                        next_direction, consecutive_steps_new = random.choice(choices), 0
                    next_note_index = (current_note_index + next_direction); rule_applied = "Default Step"
                else:
                    jump = random.choice([-5, -4, -2, 2, 4, 5]); next_note_index, next_direction, consecutive_steps_new = (current_note_index + jump), np.sign(jump), 0; rule_applied = "Default Leap"
        
        log_callback(f"    Rule Applied: {rule_applied}", 'debug', debug_only=True)
        next_note_index = max(0, min(scale_length - 1, next_note_index))
        return next_note_index, next_direction, consecutive_steps_new

    def _generate_bass_line_note(self, current_chord_indices): return current_chord_indices[0] if random.random() < 0.8 else random.choice(current_chord_indices[1:3])

    def _karplus_strong(self, freq, duration, sample_rate):
        """Generates a plucked string sound using the Karplus-Strong algorithm."""
        wavetable_size = sample_rate // freq
        wavetable = np.random.uniform(-1, 1, int(wavetable_size))
        num_samples = int(duration * sample_rate)
        samples = np.zeros(num_samples)
        current_sample = 0
        previous_value = 0
        while current_sample < num_samples:
            wavetable_index = current_sample % int(wavetable_size)
            r = np.random.binomial(1, 0.5) # a bit of randomness
            samples[current_sample] = wavetable[wavetable_index]
            wavetable[wavetable_index] = (wavetable[wavetable_index] + previous_value) / 2 * (0.99 + r * 0.005) # decay with randomness
            previous_value = samples[current_sample]
            current_sample += 1
        return samples
        
    def _generate_rich_saw(self, freq, duration, sample_rate, num_harmonics=8, detune_factor=0.01):
        """Generates a richer, detuned sawtooth-like wave."""
        t = np.linspace(0, duration, int(duration * sample_rate), False)
        wave = np.zeros_like(t)
        # LFO for vibrato
        lfo_freq = 5 # Vibrato speed
        lfo_depth = 0.005 # Vibrato depth
        lfo = lfo_depth * np.sin(2 * np.pi * lfo_freq * t)

        for i in range(1, num_harmonics + 1):
            detune = 1 + (random.random() - 0.5) * detune_factor
            amplitude = 1.0 / i
            wave += amplitude * signal.sawtooth(2 * np.pi * freq * i * detune * (1 + lfo) * t)
        
        return wave / num_harmonics
        
    def _generate_fm_ep(self, freq, duration, sample_rate):
        """Generates a Rhodes-like electric piano sound using 2-operator FM synthesis."""
        num_samples = int(duration * sample_rate)
        t = np.linspace(0, duration, num_samples, False)
        
        carrier_freq = freq
        modulator_freq = freq * 1.414 # Non-integer ratio for metallic sound
        mod_index = 2.0 # Modulation depth
        
        # Proportional envelope to prevent errors with short notes
        attack_prop = 0.02; decay_prop = 0.4; release_prop = 0.3
        sustain_level = 0.1

        attack_samples = int(attack_prop * num_samples)
        release_samples = int(release_prop * num_samples)
        decay_samples = int(decay_prop * num_samples)
        sustain_samples = num_samples - attack_samples - decay_samples - release_samples

        if sustain_samples < 0:
            total_ads = attack_samples + decay_samples + release_samples
            if total_ads == 0: return np.zeros(num_samples) # Avoid division by zero for extremely short notes
            attack_samples = int(attack_samples / total_ads * num_samples)
            decay_samples = int(decay_samples / total_ads * num_samples)
            release_samples = num_samples - attack_samples - decay_samples
            sustain_samples = 0
            
        env = np.concatenate([
            np.linspace(0, 1, attack_samples) if attack_samples > 0 else [],
            np.linspace(1, sustain_level, decay_samples) if decay_samples > 0 else [],
            np.full(sustain_samples, sustain_level) if sustain_samples > 0 else [],
            np.linspace(sustain_level, 0, release_samples) if release_samples > 0 else []
        ])
        
        modulator = env * mod_index * np.sin(2 * np.pi * modulator_freq * t)
        carrier = np.sin(2 * np.pi * carrier_freq * t + modulator)
        
        return carrier * env
        
    def _generate_synth_pad(self, freq, duration, sample_rate):
        """Generates a synth pad using subtractive synthesis."""
        num_samples = int(duration * sample_rate)
        t = np.linspace(0, duration, num_samples, False)
        
        raw_wave = self._generate_rich_saw(freq, duration, sample_rate, num_harmonics=10, detune_factor=0.02)
        
        cutoff_start, cutoff_end = 5000, 800
        cutoff_env = np.linspace(cutoff_start, cutoff_end, num_samples)
        
        filtered_wave = np.zeros_like(raw_wave)
        
        chunk_size = 256
        for i in range(0, num_samples, chunk_size):
            chunk = raw_wave[i:i+chunk_size]
            cutoff = cutoff_env[i]
            b, a = signal.butter(4, max(20, cutoff) / (0.5 * sample_rate), btype='low')
            filtered_wave[i:i+chunk_size] = signal.lfilter(b, a, chunk)

        # Proportional envelope
        attack_prop = 0.3; release_prop = 0.5
        attack_samples = int(attack_prop * num_samples)
        release_samples = int(release_prop * num_samples)
        sustain_samples = num_samples - attack_samples - release_samples
        if sustain_samples < 0:
             if (attack_samples + release_samples) == 0: return np.zeros(num_samples)
             attack_samples = int(attack_samples / (attack_samples+release_samples) * num_samples)
             release_samples = num_samples - attack_samples
             sustain_samples = 0

        pad_env = np.concatenate([
            np.linspace(0, 1, attack_samples) if attack_samples > 0 else [],
            np.full(sustain_samples, 1.0) if sustain_samples > 0 else [],
            np.linspace(1, 0, release_samples) if release_samples > 0 else []
        ])
        
        return filtered_wave * pad_env
    
    def _generate_drawbar_organ(self, freq, duration, sample_rate):
        num_samples = int(duration * sample_rate)
        t = np.linspace(0, duration, num_samples, False)
        
        # Hammond B3-style drawbar ratios (harmonics) and amplitudes
        harmonics = {1: 0.8, 2: 0.6, 3: 0.5, 4: 0.4, 6: 0.3, 8: 0.2} # 1st, 2nd, 3rd, 4th, 6th, 8th
        total_amp = sum(harmonics.values())
        
        organ_wave = np.zeros(num_samples)
        for harmonic, amp in harmonics.items():
            organ_wave += (amp / total_amp) * np.sin(2 * np.pi * freq * harmonic * t)
            
        # Add a gentle tremolo (amplitude modulation)
        lfo_freq = 7 # Hz
        tremolo = 1 - 0.1 * np.sin(2 * np.pi * lfo_freq * t)
        
        # Simple attack/release envelope
        attack_time = 0.01; release_time = 0.05
        attack_samples = min(int(attack_time*sample_rate), num_samples//2)
        release_samples = min(int(release_time*sample_rate), num_samples//2)
        sustain_samples = num_samples - attack_samples - release_samples
        
        env = np.concatenate([
            np.linspace(0, 1, attack_samples) if attack_samples > 0 else [],
            np.ones(sustain_samples) if sustain_samples > 0 else [],
            np.linspace(1, 0, release_samples) if release_samples > 0 else []
        ])
        
        return organ_wave * tremolo * env

    def _generate_pluck_synth(self, freq, duration, sample_rate):
        num_samples = int(duration * sample_rate)
        t = np.linspace(0, duration, num_samples, False)
        
        # Sawtooth wave is good for plucks
        raw_wave = signal.sawtooth(2 * np.pi * freq * t)
        
        # A very sharp AD (Attack-Decay) envelope
        decay_rate = 30.0
        env = np.exp(-decay_rate * t) * (1 - np.exp(-150.0 * t))
        
        return raw_wave * env

    def _generate_hollow_square(self, freq, duration, sample_rate):
        num_samples = int(duration * sample_rate)
        t = np.linspace(0, duration, num_samples, False)
        
        # PWM simulation by phase shifting
        phase_shift = np.pi / 2.5
        wave1 = signal.square(2 * np.pi * freq * t)
        wave2 = signal.square(2 * np.pi * freq * t + phase_shift)
        
        # Low-pass filter to smooth the sound
        b, a = signal.butter(2, 2500 / (0.5 * sample_rate), btype='low')
        filtered_wave = signal.lfilter(b, a, wave1 + wave2)
        
        # Envelope
        attack_time = 0.02; release_time = 0.1
        attack_samples = min(int(attack_time*sample_rate), num_samples//2)
        release_samples = min(int(release_time*sample_rate), num_samples//2)
        sustain_samples = num_samples - attack_samples - release_samples
        env = np.concatenate([
            np.linspace(0, 1, attack_samples) if attack_samples > 0 else [],
            np.ones(sustain_samples) if sustain_samples > 0 else [],
            np.linspace(1, 0, release_samples) if release_samples > 0 else []
        ])
        return filtered_wave * env
        
    def _generate_brass_ensemble(self, freq, duration, sample_rate):
        num_samples = int(duration * sample_rate)
        t = np.linspace(0, duration, num_samples, False)
        
        # Rich saw wave as the source
        raw_wave = self._generate_rich_saw(freq, duration, sample_rate, num_harmonics=12, detune_factor=0.03)
        
        # Filter with an envelope
        attack_time = 0.05; decay_time = 0.2
        attack_samples = int(attack_time * num_samples)
        decay_samples = int(decay_time * num_samples)
        
        filter_env = np.concatenate([
            np.linspace(400, 3000, attack_samples) if attack_samples > 0 else [],
            np.geomspace(3000, 1500, decay_samples) if decay_samples > 0 else [],
            np.full(num_samples - attack_samples - decay_samples, 1500)
        ])
        
        filtered_wave = np.zeros_like(raw_wave)
        chunk_size = 128
        for i in range(0, num_samples, chunk_size):
            chunk = raw_wave[i:i+chunk_size]
            cutoff = filter_env[i]
            b, a = signal.butter(2, max(20, cutoff) / (0.5 * sample_rate), btype='low')
            filtered_wave[i:i+chunk_size] = signal.lfilter(b, a, chunk)
            
        # Amplitude envelope
        amp_env = np.concatenate([
            np.linspace(0, 1, attack_samples) if attack_samples > 0 else [],
            np.geomspace(1, 0.8, decay_samples) if decay_samples > 0 else [],
            np.full(num_samples - attack_samples - decay_samples, 0.8)
        ])
        
        return filtered_wave * amp_env


    def _generate_tone(self, duration_sec, sample_rate, freqs, waveform_type):
        if not isinstance(freqs, list): freqs = [freqs]
        num_samples = int(duration_sec * sample_rate)
        if num_samples <= 0: return np.zeros(0) # Guard against negative or zero samples
        t = np.linspace(0, duration_sec, num_samples, False)
        
        combined_audio = np.zeros(num_samples)
        if not freqs: return combined_audio

        for frequency in freqs:
            if waveform_type == 'Square': audio_data = np.sign(np.sin(frequency * t * 2 * np.pi))
            elif waveform_type == 'Sawtooth': audio_data = signal.sawtooth(2 * np.pi * frequency * t)
            elif waveform_type == 'Triangle': audio_data = signal.sawtooth(2 * np.pi * frequency * t, width=0.5)
            elif waveform_type == 'Piano':
                harmonics = {1:1.0, 2:0.5, 3:0.3, 4:0.2, 5:0.15, 6:0.1, 8:0.05}
                total_amplitude = sum(harmonics.values())
                audio_data = np.zeros(num_samples)
                env = np.exp(-5.0 * t) * (1 - np.exp(-30.0 * t))
                for i, amp in harmonics.items():
                    harmonic_freq = frequency * i * (1 + (i-1)*0.0005) # Inharmonicity
                    audio_data += (amp/total_amplitude) * np.sin(harmonic_freq * t * 2 * np.pi)
                audio_data *= env
            elif waveform_type == 'Karplus-Strong':
                audio_data = self._karplus_strong(frequency, duration_sec, sample_rate)
            elif waveform_type == 'Rich Saw':
                audio_data = self._generate_rich_saw(frequency, duration_sec, sample_rate)
            elif waveform_type == 'FM E-Piano':
                audio_data = self._generate_fm_ep(frequency, duration_sec, sample_rate)
            elif waveform_type == 'Synth Pad':
                audio_data = self._generate_synth_pad(frequency, duration_sec, sample_rate)
            elif waveform_type == 'Drawbar Organ':
                audio_data = self._generate_drawbar_organ(frequency, duration_sec, sample_rate)
            elif waveform_type == 'Pluck Synth':
                audio_data = self._generate_pluck_synth(frequency, duration_sec, sample_rate)
            elif waveform_type == 'Hollow Square':
                audio_data = self._generate_hollow_square(frequency, duration_sec, sample_rate)
            elif waveform_type == 'Brass Ensemble':
                audio_data = self._generate_brass_ensemble(frequency, duration_sec, sample_rate)
            else: # Sine wave
                audio_data = np.sin(frequency * t * 2 * np.pi)
            combined_audio += audio_data

        return combined_audio / len(freqs) if freqs else np.zeros(num_samples)

    def _generate_kick(self, duration_sec, sample_rate):
        num_samples = int(duration_sec * sample_rate)
        t = np.linspace(0, duration_sec, num_samples, False)
        
        # Pitch sweep for the "thump"
        start_freq, end_freq = 120, 40
        pitch_env = np.geomspace(start_freq, end_freq, num_samples)
        thump = np.sin(2 * np.pi * np.cumsum(pitch_env) / sample_rate)
        
        # Amplitude envelope for the thump
        thump_env = np.exp(-25.0 * t)
        
        # Noise for the "click"
        click_noise = np.random.uniform(-1, 1, num_samples)
        b, a = signal.butter(2, 2000/(0.5*sample_rate), btype='high')
        filtered_click = signal.lfilter(b, a, click_noise)
        click_env = np.exp(-200.0 * t)
        
        return (thump * thump_env * 0.9) + (filtered_click * click_env * 0.1)

    def _generate_snare(self, duration_sec, sample_rate):
        # --- BUG FIX: Changed 'duration' to 'duration_sec' ---
        num_samples = int(duration_sec * sample_rate)
        t = np.linspace(0, duration_sec, num_samples, False)

        # Tonal body
        body_tone = np.sin(2 * np.pi * 180 * t) + np.sin(2 * np.pi * 280 * t)
        body_env = np.exp(-30.0 * t)

        # Noise for the "snap"
        snap_noise = np.random.uniform(-1, 1, num_samples)
        b, a = signal.butter(4, 1500/(0.5*sample_rate), btype='high')
        filtered_snap = signal.lfilter(b, a, snap_noise)
        snap_env = np.exp(-40.0 * t)

        return (body_tone * body_env * 0.3) + (filtered_snap * snap_env * 0.7)

    def _generate_hi_hat(self, duration_sec, sample_rate, is_open=False):
        num_samples = int(duration_sec * sample_rate)
        
        # Metallic sound from multiple square waves
        raw_sound = np.zeros(num_samples)
        for freq in [3000, 4700, 6800, 8500, 9800]:
            raw_sound += signal.square(2 * np.pi * freq * np.linspace(0, duration_sec, num_samples, False))
            
        b, a = signal.butter(6, 6000/(0.5*sample_rate), btype='high')
        filtered_sound = signal.lfilter(b, a, raw_sound)
        
        decay_rate = 15.0 if is_open else 80.0
        env = np.exp(-decay_rate * np.linspace(0, duration_sec, num_samples, False))
        
        return filtered_sound * env


    def _generate_percussion_sound(self, drum_type, duration_sec, sample_rate):
        if duration_sec <= 0: return np.zeros(0)
        if drum_type == 'kick':
            return self._generate_kick(duration_sec, sample_rate)
        elif drum_type == 'snare':
            return self._generate_snare(duration_sec, sample_rate)
        elif drum_type == 'hihat_closed':
            return self._generate_hi_hat(duration_sec, sample_rate, is_open=False)
        elif drum_type == 'hihat_open':
            return self._generate_hi_hat(duration_sec, sample_rate, is_open=True)
        # Fallback for tom and crash using simpler method for now
        elif drum_type == 'tom':
            return self._generate_tone(duration_sec, sample_rate, [120], 'Sine') * np.exp(-20.0 * np.linspace(0, duration_sec, int(duration_sec * sample_rate), False))
        elif drum_type == 'crash':
            noise = np.random.uniform(-1, 1, int(duration_sec * sample_rate))
            b, a = signal.butter(8, 4000/(0.5*sample_rate), btype='high')
            return signal.lfilter(b, a, noise) * np.exp(-4.0 * np.linspace(0, duration_sec, int(duration_sec * sample_rate), False))
        return np.zeros(int(duration_sec*sample_rate))

    def _generate_dynamic_drum_rhythm(self, section_name, section_duration, drum_bpm, song_style, tension):
        drum_track_data = []
        beat_duration = 60.0 / drum_bpm
        
        swing_factor = random.uniform(0.01, 0.08)
        humanization_factor = beat_duration * 0.05
        
        num_measures = int(section_duration / (beat_duration * 4))
        
        for measure in range(num_measures):
            # Tension increases chance of a fill
            is_fill_measure = (measure + 1) % 4 == 0 and random.random() < (0.15 + tension * 0.3)
            pattern_type = 'fill' if is_fill_measure else 'main'
            pattern = self.DRUM_PATTERNS[song_style][pattern_type]
            
            measure_start_time = measure * beat_duration * 4
            
            # Place crash on hyper-downbeat of high-tension sections
            if measure % 4 == 0 and tension > 0.7 and random.random() < 0.6:
                drum_track_data.append({'start_time': measure_start_time, 'duration': beat_duration * 2, 'drum_type': 'crash', 'volume': 0.8 * self.DRUM_MIX_VOLUMES.get('crash', 1.0)})

            for beat, drum_type in pattern:
                base_hit_time = measure_start_time + (beat * beat_duration)
                
                is_off_beat = beat % 0.5 != 0
                swing_delay = (beat_duration * swing_factor) if is_off_beat else 0
                humanization_offset = random.uniform(-humanization_factor, humanization_factor)
                hit_time = max(0, base_hit_time + swing_delay + humanization_offset)

                beat_in_measure = beat % 4
                if beat_in_measure == 0: base_volume = 1.0
                elif beat_in_measure == 2: base_volume = 0.85
                else: base_volume = 0.7
                
                final_volume = base_volume * self.DRUM_MIX_VOLUMES.get(drum_type, 1.0)
                
                duration = beat_duration * 0.5 if 'open' in drum_type or 'crash' in drum_type else beat_duration * 0.25
                if hit_time < (measure + 1) * beat_duration * 4:
                    drum_track_data.append({'start_time': hit_time, 'duration': duration, 'drum_type': drum_type, 'volume': final_volume})

        return drum_track_data

    # --- REFINED: Rhythmic generation using motifs ---
    def _get_rhythm_sequence(self, total_beats, tension=0.5, exclude_motif=None):
        sequence = []
        beats_generated = 0
        
        # Higher tension -> more complex rhythm
        if tension > 0.7:
            motif_choices = ['syncopated', 'gallop', 'offbeat']
        elif tension > 0.4:
            motif_choices = ['straight', 'dotted', 'offbeat']
        else:
            motif_choices = ['straight', 'dotted']
        
        if exclude_motif and len(motif_choices) > 1:
            motif_choices = [m for m in motif_choices if m != exclude_motif]

        motif_name = random.choice(motif_choices)
        motif = self.RHYTHMIC_MOTIFS[motif_name]
        
        while beats_generated < total_beats:
            for duration in motif:
                if beats_generated + duration > total_beats:
                    # Adjust the last note to fit the remaining time
                    final_duration = total_beats - beats_generated
                    if final_duration > 0:
                        sequence.append(final_duration)
                    beats_generated = total_beats
                    break
                
                sequence.append(duration)
                beats_generated += duration

            # Add a chance for a rest between motifs
            if beats_generated < total_beats and random.random() < 0.3:
                rest_duration = 0.5
                if beats_generated + rest_duration <= total_beats:
                    sequence.append(-rest_duration) # Negative for rests
                    beats_generated += rest_duration
        
        return [sequence], motif_name # Return as a single phrase for simplicity

    def _apply_schema(self, start_idx, schema_name, scale_notes, beat_duration):
        schema = self.CLASSICAL_SCHEMAS[schema_name]
        events = []
        current_time = 0
        for i, step in enumerate(schema['pattern']):
            note_idx = max(0, min(len(scale_notes) - 1, start_idx + step))
            duration = schema['durations'][i] * beat_duration
            events.append({'duration': duration, 'freqs': [scale_notes[note_idx]], 'scale_idx': [note_idx]})
            current_time += duration
        return events

    def _build_harmony_figure(self, base_note_idx, scale_len, base_scale_len, dissonance_level, current_chord_indices):
        # --- REVISED: Constrain harmony figures to chord tones ---
        num_notes = random.choices([1, 2, 3], weights=[0.7, 0.25, 0.05])[0]
        if num_notes == 1:
            return [base_note_idx]

        notes = [base_note_idx]
        # Get the chord tones in the same octave as the base note
        octave_offset = (base_note_idx // base_scale_len) * base_scale_len
        chord_tones_in_octave = [idx + octave_offset for idx in current_chord_indices]
        
        for _ in range(num_notes - 1):
            # Choose another chord tone from the current chord
            new_note = random.choice(chord_tones_in_octave)
            # Add a chance to shift it by an octave
            if random.random() < 0.3:
                new_note += random.choice([-1, 1]) * base_scale_len
            
            new_note = max(0, min(scale_len - 1, new_note))
            if new_note not in notes:
                notes.append(new_note)
        
        return sorted(list(set(notes)))

    def _get_waveform(self, var):
        val = var.get()
        if val == "Random":
            return random.choice(["Sine", "Piano", "Karplus-Strong", "Rich Saw", "FM E-Piano", "Synth Pad", "Drawbar Organ", "Pluck Synth", "Brass Ensemble"])
        return val
        
    def _generate_structural_melody(self, chord_progression_indices, base_scale_len):
        structural_notes = []
        for chord_indices in chord_progression_indices:
            if not chord_indices:
                structural_notes.append(None)
                continue
            structural_note = random.choice(chord_indices) + (base_scale_len * 2)
            structural_notes.append(structural_note)
        return structural_notes

    def _apply_modal_interchange(self, progression, scale_type):
        if random.random() > 0.25 or scale_type not in self.MODAL_INTERCHANGE_MAP:
            return progression
        
        new_progression = progression[:]
        interchange_options = self.MODAL_INTERCHANGE_MAP[scale_type]
        
        eligible_indices = [i for i, chord in enumerate(new_progression) if chord in interchange_options]
        
        if eligible_indices:
            idx_to_change = random.choice(eligible_indices)
            original_chord = new_progression[idx_to_change]
            new_progression[idx_to_change] = interchange_options[original_chord]
            self.update_log(f"Modal Interchange: Changed {original_chord} to {new_progression[idx_to_change]}", 'main')
        
        return new_progression

    def _generate_thematic_seed(self):
        num_notes = random.randint(3, 5)
        seed = []
        last_interval = 0
        for _ in range(num_notes):
            interval = random.choice([-2, -1, -1, 1, 1, 2, 3])
            if interval == -last_interval and abs(last_interval) > 1: pass
            elif interval == 0: interval = random.choice([-1, 1])
            duration = random.choice([0.25, 0.5, 0.5, 1.0])
            seed.append({'interval': interval, 'duration': duration})
            last_interval = interval
        self.thematic_seed = seed
        self.update_log(f"Generated thematic seed: {seed}", 'debug', debug_only=True)

    def _transform_and_apply_seed(self, start_idx, start_time, beat_duration, scale, waveform, volume):
        if not self.thematic_seed: return [], start_idx, start_time
        
        events = []
        current_idx, current_time = start_idx, start_time
        transformation = random.choice(['none', 'inversion', 'augmentation', 'diminution', 'retrograde', 'sequence_up', 'sequence_down'])
        self.update_log(f"Applying thematic seed with transformation: {transformation}", "debug", debug_only=True)

        seed_to_use = copy.deepcopy(self.thematic_seed)
        
        if transformation == 'retrograde': seed_to_use.reverse()
        elif transformation == 'sequence_up': current_idx += 2
        elif transformation == 'sequence_down': current_idx -= 2

        for note in seed_to_use:
            interval, duration = note['interval'], note['duration']
            if transformation == 'inversion': interval *= -1
            elif transformation == 'augmentation': duration *= 2
            elif transformation == 'diminution': duration /= 2
            
            current_idx = max(0, min(len(scale) - 1, current_idx + interval))
            event = {'start_time': current_time, 'duration': duration * beat_duration, 'freqs': [scale[current_idx]], 'scale_idx': [current_idx], 'articulation': 1.0, 'volume': volume, 'waveform': waveform}
            events.append(event)
            current_time += duration * beat_duration
            
        return events, current_idx, current_time
    
    def _apply_cadence(self, progression, scale_type):
        if len(progression) < 2 or random.random() < 0.2: return progression
        new_prog = progression[:-2]
        if "Major" in scale_type: new_prog.extend(['V', 'I'])
        else: new_prog.extend(['v', 'i'])
        return new_prog

    # --- NEW: Voice leading function ---
    def _apply_voice_leading(self, last_chord_indices, current_chord_indices, base_scale_len):
        if not last_chord_indices or not current_chord_indices:
            return current_chord_indices

        new_chord_indices = []
        for target_note in current_chord_indices:
            # Find the octave of the target note that is closest to any note in the last chord
            min_dist = float('inf')
            best_note = target_note
            for last_note in last_chord_indices:
                octave_multiple = round((last_note - target_note) / base_scale_len)
                candidate_note = target_note + (octave_multiple * base_scale_len)
                dist = abs(candidate_note - last_note)
                if dist < min_dist:
                    min_dist = dist
                    best_note = candidate_note
            new_chord_indices.append(best_note)
        
        return sorted(list(set(new_chord_indices)))

    # --- NEW: Refined Ornamentation System ---
    def _apply_ornamentation(self, melody_events, scale_notes, beat_duration, tension):
        if tension < 0.4: return melody_events, []
        
        ornamented_events = []
        ornament_times = []
        
        for i, event in enumerate(melody_events):
            ornamented_events.append(event)
            
            # Conditions for applying an ornament
            is_long_note = event['duration'] >= beat_duration * 0.9
            is_strong_beat = (event['start_time'] / beat_duration) % 1 == 0
            should_ornament = random.random() < (tension - 0.3)
            
            if not should_ornament or not event.get('scale_idx'):
                continue
                
            main_note_idx = event['scale_idx'][0]
            ornament_type = random.choice(['acciaccatura', 'mordent', 'turn'] if is_long_note else ['acciaccatura', 'mordent'])
            
            # --- Acciaccatura (Grace Note) ---
            if ornament_type == 'acciaccatura' and main_note_idx > 0:
                grace_duration = 0.05
                if event['duration'] > grace_duration:
                    event['duration'] -= grace_duration
                    event['start_time'] += grace_duration
                    grace_note_idx = main_note_idx - 1
                    grace_event = copy.deepcopy(event)
                    grace_event.update({'start_time': event['start_time'] - grace_duration, 'duration': grace_duration, 'scale_idx': [grace_note_idx], 'freqs': [scale_notes[grace_note_idx]]})
                    ornamented_events.insert(-1, grace_event)
                    ornament_times.append(grace_event['start_time'])

            # --- Mordent ---
            elif ornament_type == 'mordent' and 0 < main_note_idx < len(scale_notes) - 1:
                ornament_dur = min(event['duration'] / 2, beat_duration / 4)
                if event['duration'] > ornament_dur * 2:
                    event['duration'] -= ornament_dur
                    neighbor_idx = main_note_idx + random.choice([-1, 1])
                    
                    mordent_note = copy.deepcopy(event)
                    mordent_note.update({'duration': ornament_dur / 2, 'scale_idx': [neighbor_idx], 'freqs': [scale_notes[neighbor_idx]]})
                    
                    return_note = copy.deepcopy(event)
                    return_note.update({'start_time': event['start_time'] + ornament_dur/2, 'duration': ornament_dur/2})
                    
                    ornamented_events.insert(-1, mordent_note)
                    ornamented_events.insert(-1, return_note)
                    ornament_times.append(event['start_time'])

            # --- Turn ---
            elif ornament_type == 'turn' and 0 < main_note_idx < len(scale_notes) - 1:
                turn_duration = min(event['duration'], beat_duration / 2)
                if event['duration'] > turn_duration:
                    event['start_time'] += turn_duration
                    event['duration'] -= turn_duration
                    note_dur = turn_duration / 4
                    
                    turn_indices = [main_note_idx + 1, main_note_idx, main_note_idx - 1, main_note_idx]
                    for j, turn_idx in enumerate(turn_indices):
                        turn_note = copy.deepcopy(event)
                        turn_note.update({'start_time': event['start_time'] - turn_duration + (j * note_dur), 'duration': note_dur, 'scale_idx': [turn_idx], 'freqs': [scale_notes[turn_idx]]})
                        ornamented_events.insert(-1, turn_note)
                    ornament_times.append(event['start_time'] - turn_duration)

        return ornamented_events, ornament_times

    def _map_chord_to_polytonal_scale(self, original_chord_indices, original_scale_notes, polytonal_scale_notes):
        mapped_indices = []
        for idx in original_chord_indices:
            original_freq = original_scale_notes[idx]
            # Find the closest frequency in the polytonal scale
            closest_freq = min(polytonal_scale_notes, key=lambda f: abs(f - original_freq))
            closest_idx = polytonal_scale_notes.index(closest_freq)
            mapped_indices.append(closest_idx)
        return mapped_indices

    def _generate_song_section_data(self, selected_scale_name, selected_scale_notes, scale_type, progression_name, section_duration, melody_bpm, log_callback, scale_notes_base, texture_mode, tension=0.5, is_heterophonic=False, is_reprise=False, is_polyrhythmic=False, is_polytonal=False):
        progression_romans_base = self.CHORD_PROGRESSIONS.get(scale_type, {}).get(progression_name, [])
        
        if not progression_romans_base:
            log_callback(f"No '{progression_name}' progression found for {scale_type}. Using fallback.", 'debug', debug_only=True)
            progression_romans_base = ['i', 'iv', 'v', 'i'] if scale_type in self.MINOR_LIKE_SCALES else ['I', 'IV', 'V', 'I']

        progression_romans = self._apply_cadence(self._apply_modal_interchange(progression_romans_base, scale_type), scale_type)
        log_callback(f"Progression for {progression_name.title()}: {progression_romans} (Section Texture: {texture_mode})", 'main')
        
        chord_progression_indices_base = [self.DIATONIC_CHORDS[scale_type].get(r, []) for r in progression_romans]
        
        melody1_events, melody2_events, bass_events, chord_events = [], [], [], []
        
        base_scale_len = len(scale_notes_base)
        structural_melody_guide = self._generate_structural_melody(chord_progression_indices_base, base_scale_len)
        characteristic_note_idx = self.MODAL_CHARACTERISTICS.get(scale_type)

        initial_chord_note_m1 = chord_progression_indices_base[0][0] if chord_progression_indices_base and chord_progression_indices_base[0] else 0
        m1_current_idx = m1_last_idx = initial_chord_note_m1 + base_scale_len * 2
        m2_current_idx = m2_last_idx = m1_last_idx - base_scale_len
        
        beat_duration = 60.0 / melody_bpm
        chord_duration = section_duration / len(chord_progression_indices_base) if chord_progression_indices_base else section_duration
        dissonance_level = 0.05 + (tension * 0.4)

        current_time = 0.0
        last_chord_indices_voic_led = []
        
        # --- NEW: Setup for Polytonality ---
        polytonal_scale_notes = selected_scale_notes
        if is_polytonal:
            related_key = self._get_related_key(selected_scale_name, 'dominant')
            polytonal_scale_base = self.MUSICAL_SCALES[related_key]
            polytonal_scale_notes = [f/2 for f in polytonal_scale_base] + polytonal_scale_base + [f*2 for f in polytonal_scale_base] + [f*4 for f in polytonal_scale_base]
            log_callback(f"Melody 2 will use polytonal key: {related_key}", 'debug', debug_only=True)

        for i, chord_indices in enumerate(chord_progression_indices_base):
            if not chord_indices: continue
            
            chord_indices_voic_led = self._apply_voice_leading(last_chord_indices_voic_led, chord_indices, base_scale_len)
            last_chord_indices_voic_led = chord_indices_voic_led
            
            target_structural_note = structural_melody_guide[i]
            chord_freqs = [selected_scale_notes[idx] for idx in chord_indices_voic_led]
            num_chord_beats = int(round(chord_duration / beat_duration))
            
            # --- MELODY 1 (Base Generation) ---
            time_m1 = current_time
            m1_events_this_chord = []
            if texture_mode != 'monophonic_breakdown' or random.random() < 0.5:
                rhythm_phrases_m1, motif1 = self._get_rhythm_sequence(num_chord_beats, tension=tension * (1.2 if is_reprise else 1.0))
                beats_elapsed = 0
                for phrase in rhythm_phrases_m1:
                    contour = random.choice(['rising', 'falling', 'arch'])
                    for beat in phrase:
                        duration = abs(beat) * beat_duration
                        if time_m1 >= current_time + chord_duration: continue
                        if beat > 0:
                            phrase_progress = beats_elapsed / sum(abs(b) for p in rhythm_phrases_m1 for b in p) if sum(abs(b) for p in rhythm_phrases_m1 for b in p) > 0 else 0
                            is_strong_beat = (beats_elapsed % 1 == 0)
                            m1_new_idx, _, _ = self._generate_melodic_note(m1_current_idx, m1_last_idx, None, selected_scale_notes, chord_indices, 0, 0, progression_name, scale_type, log_callback, contour, phrase_progress, target_note_idx=target_structural_note, is_strong_beat=is_strong_beat, characteristic_note_idx=characteristic_note_idx)
                            m1_figure = self._build_harmony_figure(m1_new_idx, len(selected_scale_notes), base_scale_len, dissonance_level, chord_indices)
                            main_event = {'start_time': time_m1, 'duration': duration, 'freqs': [selected_scale_notes[i] for i in m1_figure], 'scale_idx': m1_figure, 'articulation': 1.0, 'volume': (0.6 + tension * 0.4), 'waveform': self.current_m1_waveform}
                            m1_events_this_chord.append(main_event)
                            m1_current_idx = m1_new_idx
                        time_m1 += duration
                        beats_elapsed += abs(beat)
            
            m1_events_this_chord, m1_ornament_times = self._apply_ornamentation(m1_events_this_chord, selected_scale_notes, beat_duration, tension)
            melody1_events.extend(m1_events_this_chord)
            
            # --- MELODY 2 (POLY/HETERO) ---
            if is_heterophonic:
                for event in m1_events_this_chord:
                    if 'scale_idx' not in event or not event['scale_idx']: continue
                    new_event = copy.deepcopy(event)
                    
                    if is_polyrhythmic and random.random() < 0.4 and new_event['duration'] > beat_duration * 0.4:
                        # Subdivide for derivative polyrhythm
                        half_dur = new_event['duration'] / 2
                        new_event['duration'] = half_dur
                        second_note_event = copy.deepcopy(new_event)
                        second_note_event['start_time'] += half_dur
                        melody2_events.append(second_note_event)

                    if is_polytonal:
                        original_idx = new_event['scale_idx'][0]
                        original_freq = selected_scale_notes[original_idx]
                        closest_poly_freq = min(polytonal_scale_notes, key=lambda f: abs(f - original_freq))
                        closest_poly_idx = polytonal_scale_notes.index(closest_poly_freq)
                        new_event['scale_idx'] = [closest_poly_idx]
                        new_event['freqs'] = [closest_poly_freq]

                    new_event['volume'] *= 0.7
                    new_event['waveform'] = self.current_m2_waveform
                    melody2_events.append(new_event)

            elif texture_mode == 'polyphonic':
                time_m2 = current_time
                rhythm_phrases_m2, _ = self._get_rhythm_sequence(num_chord_beats, tension=tension*0.8, exclude_motif=motif1 if is_polyrhythmic else None)
                
                polytonal_chord_indices = self._map_chord_to_polytonal_scale(chord_indices, selected_scale_notes, polytonal_scale_notes) if is_polytonal else chord_indices
                
                for phrase in rhythm_phrases_m2:
                    for beat in phrase:
                        duration = abs(beat) * beat_duration
                        if time_m2 >= current_time + chord_duration: continue
                        
                        response_action = 'none'
                        if m1_ornament_times and time_m2 >= m1_ornament_times[-1] and (time_m2 - m1_ornament_times[-1]) < beat_duration * 2:
                            response_action = random.choice(['hocket', 'rhythmic_ack'])
                            m1_ornament_times.pop()
                            log_callback(f"Melody2 responding with: {response_action}", 'debug', debug_only=True)

                        if beat > 0 and response_action != 'hocket':
                            m2_new_idx, _, _ = self._generate_melodic_note(m2_current_idx, m2_last_idx, None, polytonal_scale_notes, polytonal_chord_indices, 0, 0, progression_name, scale_type, log_callback, 'arch', 0.5)
                            m2_figure = self._build_harmony_figure(m2_new_idx, len(polytonal_scale_notes), base_scale_len, dissonance_level, polytonal_chord_indices)
                            
                            event_volume = (0.5 + tension * 0.4)
                            event_duration = duration
                            if response_action == 'rhythmic_ack':
                                event_volume *= 1.2
                                event_duration *= 0.5
                            
                            melody2_events.append({'start_time': time_m2, 'duration': event_duration, 'freqs': [polytonal_scale_notes[i] for i in m2_figure], 'scale_idx': m2_figure, 'articulation': 1.0, 'volume': event_volume, 'waveform': self.current_m2_waveform})
                            m2_current_idx = m2_new_idx
                        
                        time_m2 += duration
            
            # --- BASS & CHORDS ---
            if texture_mode not in ['monophonic_breakdown']:
                bass_note_idx = self._generate_bass_line_note(chord_indices_voic_led)
                bass_events.append({'start_time': current_time, 'duration': chord_duration, 'freqs': [selected_scale_notes[bass_note_idx % base_scale_len]], 'volume': (0.7 + tension * 0.3), 'articulation': 1.0, 'waveform': self.current_bass_waveform})
                chord_events.append({'start_time': current_time, 'duration': chord_duration, 'freqs': chord_freqs, 'volume': (0.5 + tension * 0.3), 'articulation': 1.0, 'waveform': self.current_chord_waveform})

            current_time += chord_duration
        return {'melody1': melody1_events, 'melody2': melody2_events, 'bass': bass_events, 'chords': chord_events}

    def _apply_fade_out(self, audio, duration_s, sample_rate):
        fade_samples = int(duration_s * sample_rate)
        if len(audio) > fade_samples: audio[-fade_samples:] *= np.linspace(1.0, 0.0, fade_samples)
        return audio

    def _apply_hybrid_envelope(self, audio_data, fade_duration_samples):
        total_samples = len(audio_data)
        fade_samples = min(fade_duration_samples, total_samples // 2)
        if fade_samples <= 1: return audio_data
        fade_in_window = np.hanning(fade_samples * 2)[:fade_samples]
        fade_out_window = np.hanning(fade_samples * 2)[fade_samples:]
        audio_data[:fade_samples] *= fade_in_window
        audio_data[total_samples - fade_samples:] *= fade_out_window
        return audio_data

    def _intelligently_select_waveforms(self, affect):
        # Bass: Simple and strong
        self.bass_waveform_var.set(random.choice(["Sine", "Square"]))

        # Chords: Rich and sustained
        if affect in ['serene', 'melancholy']:
            self.chord_waveform_var.set(random.choice(["Synth Pad", "Drawbar Organ"]))
        else:
            self.chord_waveform_var.set(random.choice(["Rich Saw", "Brass Ensemble"]))
        
        # Melody 1 (Lead): Clear and distinct
        if affect == 'uplifting': m1_choice = random.choice(["Piano", "Brass Ensemble", "Rich Saw"])
        elif affect == 'melancholy': m1_choice = random.choice(["Karplus-Strong", "Hollow Square", "Piano"])
        elif affect == 'serene': m1_choice = random.choice(["FM E-Piano", "Sine", "Hollow Square"])
        else: # intense
            m1_choice = random.choice(["Rich Saw", "Pluck Synth", "Brass Ensemble"])
        self.melody1_waveform_var.set(m1_choice)

        # Melody 2 (Counterpart): Contrasting and complementary
        if m1_choice == "Piano": self.melody2_waveform_var.set(random.choice(["Sine", "Hollow Square", "Karplus-Strong"]))
        elif m1_choice == "Rich Saw": self.melody2_waveform_var.set(random.choice(["Pluck Synth", "Sine"]))
        else: self.melody2_waveform_var.set("Sine") # Safe default
        
        self.update_log("Auto-selected waveforms based on affect.", 'main')


    def _generate_full_song(self):
        if self.ui_mode:
            total_duration = int(self.entry_duration.get())
            self.last_bit_depth = int(self.bit_depth_var.get())
        else:
            total_duration = int(self.settings.get("duration", 90))
            self.last_bit_depth = int(self.settings.get("bit_depth", 24))

        self.last_sample_rate = 44100
        self._generate_thematic_seed()

        song_affect = random.choice(['uplifting', 'melancholy', 'serene', 'intense'])
        
        if song_affect == 'uplifting':
            melody_bpm = random.randint(120, 160); affect_scale_choices = ["Major", "Pentatonic Major", "Lydian", "Mixolydian"]
        elif song_affect == 'melancholy':
            melody_bpm = random.randint(70, 110); affect_scale_choices = ["Minor", "Harmonic Minor", "Dorian"]
        elif song_affect == 'serene':
            melody_bpm = random.randint(60, 90); affect_scale_choices = ["Custom", "Pentatonic Major", "Lydian"]
        else: # intense
            melody_bpm = random.randint(130, 180); affect_scale_choices = ["Phrygian Dominant", "Blues", "Melodic Minor", "Phrygian", "Locrian"]

        beat_duration = 60.0 / melody_bpm
        log_callback = self.update_log
        
        user_enabled_scales = [st for st, var in self.scale_vars.items() if var.get()]
        if not user_enabled_scales: user_enabled_scales = ["Major"]
        final_scale_choices = [s for s in user_enabled_scales if s in affect_scale_choices]
        if not final_scale_choices: final_scale_choices = user_enabled_scales
        
        possible_scales = [name for name in self.MUSICAL_SCALES.keys() if name.split(' ', 1)[1] in final_scale_choices]
        selected_scale_name = random.choice(possible_scales) if possible_scales else "C Major"

        if self.ui_mode and self.auto_wave_var.get():
            self._intelligently_select_waveforms(song_affect)
            
        texture_type = random.choices(['homophonic', 'polyphonic', 'heterophonic'], weights=[3, 3, 3])[0]
        is_polyphonic = (texture_type == 'polyphonic')
        is_heterophonic = (texture_type == 'heterophonic')
        is_polyrhythmic = (texture_type != 'homophonic') and random.random() < 0.5
        is_polytonal = (texture_type != 'homophonic') and random.random() < 0.4


        log_callback(f"Generating {total_duration}s of music...", 'main')
        log_callback(f"Affect: {song_affect}, Texture: {texture_type.capitalize()}, Polyrhythmic: {is_polyrhythmic}, Polytonal: {is_polytonal}", 'main')
        
        self.current_m1_waveform = self._get_waveform(self.melody1_waveform_var)
        self.current_m2_waveform = self._get_waveform(self.melody2_waveform_var)
        self.current_chord_waveform = self._get_waveform(self.chord_waveform_var)
        self.current_bass_waveform = self._get_waveform(self.bass_waveform_var)
        
        song_form = random.choice(["Standard", "Ternary", "Rondo", "Sonata", "AABA"])
        drum_style = random.choice(list(self.DRUM_PATTERNS.keys()))
        log_callback(f"Key: {selected_scale_name}, Tempo: {melody_bpm} BPM, Form: {song_form}, Style: {drum_style}", 'main')

        structure = []
        section_map = {}
        
        if song_form == "Ternary": structure = ['A', 'B', 'A_reprise']
        elif song_form == "Rondo": structure = ['A', 'B', 'A_reprise', 'C', 'A_reprise']
        elif song_form == "AABA": structure = ['A', 'A_reprise', 'B', 'A_reprise']
        elif song_form == "Sonata":
            structure = ['Exposition_A', 'Exposition_B', 'Development', 'Recap_A', 'Recap_B']
            dominant_key = self._get_related_key(selected_scale_name, 'dominant')
            section_map = {
                'Exposition_A': {'prog': 'verse', 'key': selected_scale_name}, 'Exposition_B': {'prog': 'chorus', 'key': dominant_key},
                'Development': {'prog': 'development', 'key': selected_scale_name}, 'Recap_A': {'prog': 'verse', 'key': selected_scale_name},
                'Recap_B': {'prog': 'chorus', 'key': selected_scale_name}
            }
        else: # Standard
            structure = ['intro', 'verse', 'chorus', 'verse', 'chorus', 'bridge', 'chorus'] if total_duration > 60 else \
                        ['chorus', 'verse', 'chorus'] if total_duration >= 45 else ['chorus', 'verse']
        
        if total_duration > 60 and 'outro' not in structure: structure.append('outro')

        tension_map = {'intro':0.2, 'verse':0.4, 'pre-chorus':0.6, 'chorus':0.9, 'bridge':0.5, 'solo':1.0, 'development':0.8, 'outro':0.3, 'a':0.4, 'b':0.6, 'c':0.8, 'exposition_a':0.4, 'exposition_b':0.7, 'recap_a':0.5, 'recap_b':0.8}
        
        section_data_cache = {}
        section_duration = total_duration / len(structure)
        full_song_data = {'melody1': [], 'melody2': [], 'bass': [], 'chords': []}
        full_drum_data = []
        current_time = 0.0
        section_log_timeline = []
        archived_phrase = None

        for i, section_name in enumerate(structure):
            progression_name = section_name.split('_')[0].lower()
            if progression_name == 'a': progression_name = 'verse'
            elif progression_name == 'b': progression_name = 'bridge'
            elif progression_name == 'c': progression_name = 'solo'
            elif progression_name.startswith(('exposition', 'recap')):
                progression_name = section_map[section_name]['prog']
            
            tension = tension_map.get(progression_name, 0.5)
            
            texture_mode = 'polyphonic' if is_polyphonic or is_heterophonic else 'homophonic'
            if tension < 0.3 and random.random() < 0.3: texture_mode = 'monophonic_breakdown'

            log_callback(f"--- Generating {section_name.title()} (as {progression_name}) ---", 'main')
            section_log_timeline.append({'start_time': current_time, 'log_type': 'main', 'message': f"--- Playing {section_name.title()} ---"})

            is_reprise = '_reprise' in section_name
            original_section_name = section_name.split('_')[0]
            
            if is_reprise and original_section_name in section_data_cache:
                section_data = copy.deepcopy(section_data_cache[original_section_name]['section'])
                drum_data = copy.deepcopy(section_data_cache[original_section_name]['drums'])
            else:
                current_key = section_map.get(section_name, {}).get('key', selected_scale_name)
                current_scale_notes_base = self.MUSICAL_SCALES[current_key]
                current_scale_type = current_key.split(' ', 1)[1]
                current_scale_notes = [f/2 for f in current_scale_notes_base] + current_scale_notes_base + [f*2 for f in current_scale_notes_base] + [f*4 for f in current_scale_notes_base]

                if current_key != selected_scale_name: log_callback(f"Modulating to key: {current_key}", 'main')

                section_data = self._generate_song_section_data(current_key, current_scale_notes, current_scale_type, progression_name, section_duration, melody_bpm, log_callback, current_scale_notes_base, texture_mode, tension=tension, is_heterophonic=is_heterophonic, is_reprise=is_reprise, is_polyrhythmic=is_polyrhythmic, is_polytonal=is_polytonal)
                drum_data = self._generate_dynamic_drum_rhythm(progression_name, section_duration, melody_bpm, drum_style, tension)
                
                if original_section_name in ['A', 'B', 'C', 'chorus', 'verse']:
                    section_data_cache[original_section_name] = {'section': section_data, 'drums': drum_data}
            
            # Add transitional drum fill
            if i < len(structure) - 1:
                fill_duration_beats = 0.5
                fill_start_time = current_time + section_duration - (fill_duration_beats * beat_duration)
                if random.random() < 0.5:
                    full_drum_data.append({'start_time': fill_start_time, 'duration': beat_duration * 0.25, 'drum_type': 'snare', 'volume': 0.8})
                    full_drum_data.append({'start_time': fill_start_time + beat_duration * 0.25, 'duration': beat_duration * 0.25, 'drum_type': 'snare', 'volume': 0.9})

            for part, events in section_data.items():
                for item in events:
                    item_copy = item.copy(); item_copy['start_time'] += current_time
                    # --- NEW: Apply dynamic contour based on tension ---
                    item_copy['volume'] = item.get('volume', 1.0) * (0.8 + tension * 0.4)
                    full_song_data[part].append(item_copy)
            
            for item in drum_data:
                item_copy = item.copy(); item_copy['start_time'] += current_time
                full_drum_data.append(item_copy)

            current_time += section_duration

        self.last_song_data, self.last_drum_data, self.last_melody_bpm = full_song_data, full_drum_data, melody_bpm
        return full_song_data, full_drum_data, section_log_timeline, 'fade_out', current_time

    def _music_generation_and_playback_thread(self, initial_melody_volume, initial_drum_volume, on_finish_callback):
        try:
            full_song_data, full_drum_data, section_log_timeline, ending_style, total_duration = self._generate_full_song()
            
            SAMPLE_RATE = self.last_sample_rate
            total_samples = int(total_duration * SAMPLE_RATE) + 10
            
            part_tracks = {part: np.zeros(total_samples, dtype=np.float64) for part in full_song_data.keys()}
            drum_track = np.zeros(total_samples, dtype=np.float64)

            FADE_DURATION_S = 0.005
            fade_samples = int(FADE_DURATION_S * SAMPLE_RATE)

            for part_name, events in full_song_data.items():
                track = part_tracks[part_name]
                for item in events:
                    segment = self._generate_tone(item['duration'], SAMPLE_RATE, item['freqs'], item['waveform'])
                    if segment.size == 0: continue
                    enveloped_segment = self._apply_hybrid_envelope(segment, fade_samples)
                    
                    start_s = int(item['start_time'] * SAMPLE_RATE)
                    end_s = start_s + len(enveloped_segment)

                    if start_s < 0 or end_s > total_samples: continue
                    
                    volume = item.get('volume', 0.7)
                    waveform_multiplier = self.WAVEFORM_DYNAMICS.get(item['waveform'], 1.0)
                    final_volume = volume * waveform_multiplier
                    track[start_s:end_s] += enveloped_segment * final_volume

            for item in full_drum_data:
                segment = self._generate_percussion_sound(item['drum_type'], item['duration'], SAMPLE_RATE)
                if segment.size == 0: continue
                
                start_s = int(item['start_time'] * SAMPLE_RATE)
                end_s = start_s + len(segment)

                if start_s < 0 or end_s > total_samples: continue
                
                if drum_track[start_s:end_s].shape == segment.shape:
                    drum_track[start_s:end_s] += segment * item.get('volume', 1.0)
                else:
                    self.update_log(f"Debug: Shape mismatch skipped. Slice: {drum_track[start_s:end_s].shape}, Segment: {segment.shape}", 'debug', debug_only=True)


            harmonic_track = np.zeros(total_samples, dtype=np.float64)
            for part in ['melody1', 'melody2', 'bass', 'chords']:
                harmonic_track += part_tracks[part]
            
            for track in [harmonic_track, drum_track]:
                max_val = np.max(np.abs(track))
                if max_val > 0: track /= max_val
            
            master_audio = harmonic_track * initial_melody_volume + drum_track * initial_drum_volume
            if ending_style == 'fade_out': master_audio = self._apply_fade_out(master_audio, 4.0, SAMPLE_RATE)
            
            max_master = np.max(np.abs(master_audio))
            if max_master > 0: master_audio /= max_master
            self.last_master_audio = master_audio

            def to_stereo_sound(track):
                # Always use 16-bit for Pygame playback to prevent static.
                track_16bit = np.clip(track, -1.0, 1.0)
                final_audio = (track_16bit * 32767.0).astype(np.int16)
                return pygame.sndarray.make_sound(np.column_stack((final_audio, final_audio)))

            self.last_harmonic_sound = to_stereo_sound(harmonic_track)
            self.last_drum_sound = to_stereo_sound(drum_track)

            self.harmonic_channel, self.drum_channel = pygame.mixer.Channel(0), pygame.mixer.Channel(1)
            self.update_melody_volume(self.melody_volume_slider.get())
            self.update_drum_volume(self.drum_volume_slider.get())
            self.harmonic_channel.play(self.last_harmonic_sound)
            self.drum_channel.play(self.last_drum_sound)
            
            log_timeline = []
            log_map = {'melody1': 'melody1', 'melody2': 'melody2', 'bass': 'bass', 'chords': 'chords'}
            for part, events in full_song_data.items():
                log_type = log_map.get(part)
                if not events or not log_type: continue
                for item in events:
                    notes_str = ', '.join(self._find_closest_note_name(f) for f in item['freqs'])
                    log_timeline.append({'start_time': item['start_time'], 'log_type': log_type, 'message': f"Time: {item['start_time']:.2f}s | {notes_str} ({item['waveform']})"})
            
            for item in full_drum_data: log_timeline.append({'start_time': item['start_time'], 'log_type': 'drums', 'message': f"Time: {item['start_time']:.2f}s | Drum: {item['drum_type']}"})

            log_timeline.extend(section_log_timeline)
            log_timeline.sort(key=lambda x: x['start_time'])
            
            self.update_log("--- Starting Playback ---", 'main')
            start_playback_time, log_index = time.time(), 0
            
            while (self.harmonic_channel.get_busy() or self.drum_channel.get_busy()) and not self.stop_event.is_set():
                elapsed_time = time.time() - start_playback_time
                while log_index < len(log_timeline) and elapsed_time >= log_timeline[log_index]['start_time']:
                    entry = log_timeline[log_index]; self.update_log(entry['message'], entry['log_type']); log_index += 1
                time.sleep(0.01)
            self.update_log("--- Playback Finished ---", 'main')

        except Exception: self.update_log(f"An unexpected error occurred:\n{traceback.format_exc()}", 'main')
        finally:
            if self.harmonic_channel: self.harmonic_channel.stop()
            if self.drum_channel: self.drum_channel.stop()
            self.master.after(0, on_finish_callback)

    def run_headless(self, loop=False):
        print("Headless mode started. Using settings from harmonizer_settings.json")
        try:
            pygame.mixer.init(frequency=44100, size=-16, channels=16, buffer=1024)
            while True:
                full_song_data, full_drum_data, section_log_timeline, ending_style, total_duration = self._generate_full_song()
                print("\n--- SONG GENERATION FINISHED, NOT IMPLEMENTED FOR HEADLESS PLAYBACK YET ---\n")
                if not loop:
                    break
                time.sleep(2)
        except KeyboardInterrupt:
            print("\nExiting.")
        finally:
            pygame.mixer.quit()

    def on_closing(self): 
        self._save_settings()
        self.stop_event.set()
        if self.ui_mode:
            pygame.mixer.quit()
            self.master.destroy()
    
    def on_playback_finished(self):
        if self.lock.locked(): self.lock.release()
        self._safe_reset_ui()
        
    def update_log(self, text, log_type='main', debug_only=False):
        if not self.ui_mode:
            log_level = 'DEBUG' if debug_only else log_type.upper()
            print(f"[{log_level}] {text}")
            return

        if self.debug_window and self.debug_window.winfo_exists():
            debug_msg = f"[{log_type.upper()}] {text}\n"
            self.debug_log_area.configure(state='normal'); self.debug_log_area.insert(tk.END, debug_msg)
            self.debug_log_area.configure(state='disabled'); self.debug_log_area.see(tk.END)
        
        if debug_only: return

        widget_map = {'main': self.main_log_area, 'melody1': self.melody1_log_area, 'melody2': self.melody2_log_area, 'bass': self.bass_log_area, 'chords': self.chord_log_area, 'drums': self.drum_log_area}
        widget = widget_map.get(log_type)
        
        if widget:
            widget.configure(state='normal'); widget.insert(tk.END, text + "\n", log_type)
            widget.configure(state='disabled'); widget.see(tk.END)
    
    def _safe_reset_ui(self):
        self.play_button.config(state=tk.NORMAL)
        self.replay_button.config(state=tk.NORMAL if self.last_drum_sound is not None else tk.DISABLED)
        self.stop_button.config(state=tk.DISABLED)
        self.export_wav_button.config(state=tk.NORMAL if self.last_master_audio is not None else tk.DISABLED)
        self.export_midi_button.config(state=tk.NORMAL if self.last_song_data is not None else tk.DISABLED)
        if self.loop_var.get() and not self.stop_event.is_set():
            self.master.after(100, self.start_music)

    def _update_and_save_melody_volume(self, vol):
        self.update_melody_volume(vol)
        self._save_settings()

    def _update_and_save_drum_volume(self, vol):
        self.update_drum_volume(vol)
        self._save_settings()

    def update_melody_volume(self, vol):
        if self.harmonic_channel: self.harmonic_channel.set_volume(float(vol) / 100.0)

    def update_drum_volume(self, vol):
        if self.drum_channel: self.drum_channel.set_volume(float(vol) / 100.0)

    def start_music(self):
        if not self.lock.acquire(blocking=False): self.update_log("Generation already in progress.", 'main'); return
            
        self.play_button.config(state=tk.DISABLED); self.replay_button.config(state=tk.DISABLED); self.stop_button.config(state=tk.NORMAL)
        self.export_wav_button.config(state=tk.DISABLED); self.export_midi_button.config(state=tk.DISABLED)
        self.stop_event.clear()
        for log in [self.main_log_area, self.melody1_log_area, self.melody2_log_area, self.bass_log_area, self.chord_log_area, self.drum_log_area]: 
            log.configure(state='normal'); log.delete('1.0', tk.END); log.configure(state='disabled')
        
        self.last_harmonic_sound, self.last_drum_sound = None, None
        
        initial_melody_volume, initial_drum_volume = self.melody_volume_slider.get() / 100.0, self.drum_volume_slider.get() / 100.0
        self.music_thread = threading.Thread(target=self._music_generation_and_playback_thread, args=(initial_melody_volume, initial_drum_volume, self.on_playback_finished)); self.music_thread.start()
    
    def replay_music(self):
        if self.last_drum_sound is None: self.update_log("No song has been generated yet.", 'main'); return
        if not self.lock.acquire(blocking=False): self.update_log("Playback already in progress.", 'main'); return

        self.play_button.config(state=tk.DISABLED); self.replay_button.config(state=tk.DISABLED); self.stop_button.config(state=tk.NORMAL)
        self.stop_event.clear()

        def playback_thread_target(on_finish_callback):
            try:
                self.harmonic_channel, self.drum_channel = pygame.mixer.Channel(0), pygame.mixer.Channel(1)
                self.update_melody_volume(self.melody_volume_slider.get()); self.update_drum_volume(self.drum_volume_slider.get())
                self.harmonic_channel.play(self.last_harmonic_sound); self.drum_channel.play(self.last_drum_sound)
                while (self.harmonic_channel.get_busy() or self.drum_channel.get_busy()) and not self.stop_event.is_set(): time.sleep(0.01)
                self.update_log("Replay Finished.", 'main')
            except Exception as e: self.update_log(f"An error occurred during replay: {e}", 'main')
            finally:
                if self.harmonic_channel: self.harmonic_channel.stop()
                if self.drum_channel: self.drum_channel.stop()
                self.master.after(0, on_finish_callback)

        self.music_thread = threading.Thread(target=playback_thread_target, args=(self.on_playback_finished,)); self.music_thread.start()

    def stop_music(self): 
        self.update_log("Stop button pressed.", "debug", debug_only=True)
        self.stop_event.set()

    def export_wav_file(self):
        if self.last_master_audio is None: self.update_log("No audio to export.", 'main'); return
        filename = filedialog.asksaveasfilename(defaultextension=".wav", filetypes=[("WAV files", "*.wav")])
        if not filename: return
        
        with wave.open(filename, 'wb') as f:
            f.setnchannels(2) # Stereo
            sampwidth = self.last_bit_depth // 8
            f.setsampwidth(sampwidth)
            f.setframerate(self.last_sample_rate)
            
            if self.last_bit_depth == 24:
                audio_data_int = (self.last_master_audio * (2**23 - 1)).astype(np.int32)
                byte_data = bytearray()
                for sample in audio_data_int:
                    packed_sample = sample.to_bytes(4, byteorder='little', signed=True)[:3]
                    byte_data.extend(packed_sample) # Left channel
                    byte_data.extend(packed_sample) # Right channel
                f.writeframes(bytes(byte_data))
            else: # 16-bit
                audio_data_int = (self.last_master_audio * 32767.0).astype(np.int16)
                f.writeframes(np.column_stack((audio_data_int, audio_data_int)).tobytes())

        self.update_log(f"Exported to {filename}", 'main')
    
    def export_midi_file(self):
        if not self.last_song_data: self.update_log("No song data to export.", 'main'); return
        filename = filedialog.asksaveasfilename(defaultextension=".mid", filetypes=[("MIDI files", "*.mid")])
        if not filename: return
        
        def freq_to_midi(f): 
            if f <= 0: return 0
            return 69 + 12 * math.log2(f / 440.0)
        
        midi = MIDIFile(5)
        beat_dur = 60.0 / self.last_melody_bpm
        for t in range(5): midi.addTempo(t, 0, self.last_melody_bpm)

        track_map = {'melody1': (0, 0), 'melody2': (1, 1), 'bass': (2, 2), 'chords': (3, 3)}
        for part, (track_num, channel) in track_map.items():
            for item in self.last_song_data[part]:
                start_beat, dur_beats = item['start_time']/beat_dur, item['duration']/beat_dur
                volume = int(item.get('volume', 0.7) * 127)
                for freq in item['freqs']:
                    midi_note = int(round(freq_to_midi(freq)))
                    if midi_note > 0: midi.addNote(track_num, channel, midi_note, start_beat, dur_beats, volume)

        for item in self.last_drum_data: 
            start_beat, dur_beats = item['start_time']/beat_dur, item['duration']/beat_dur
            volume = int(item.get('volume', 0.8) * 127)
            midi_note = self.DRUM_SOUND_PROPERTIES[item['drum_type']]['midi_note']
            midi.addNote(4, 9, midi_note, start_beat, dur_beats, volume)
        
        with open(filename, "wb") as f: midi.writeFile(f)
        self.update_log(f"Exported to {filename}", 'main')
    
    def reload_script(self):
        self.stop_music()
        pygame.mixer.quit()
        self.master.destroy()
        os.execl(sys.executable, sys.executable, *sys.argv)

if __name__ == "__main__":
    if '--no-ui' in sys.argv:
        app = HarmonizerApp(master=None, ui_mode=False)
        should_loop = '--loop' in sys.argv
        app.run_headless(loop=should_loop)
    else:
        root = tk.Tk()
        app = HarmonizerApp(root)
        root.mainloop()
