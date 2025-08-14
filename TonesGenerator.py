# First, you'll need to install the pygame and scipy libraries:
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
            master.title("Harmonizer (V3.9 Logic)")
            master.geometry("750x760")
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
        self.last_bit_depth, self.last_sample_rate = 16, 44100
        
        self.last_harmonic_sound, self.last_drum_sound = None, None

        # --- Debug Window ---
        self.debug_window = None
        self.debug_log_area = None

        # --- Parameters, constants, and helper dictionaries ---
        self.NOTE_FREQUENCIES = {
            'C': 261.63, 'C#': 277.18, 'D': 293.66, 'D#': 311.13, 'E': 329.63, 'F': 349.23,
            'F#': 369.99, 'G': 392.00, 'G#': 415.30, 'A': 440.00, 'A#': 466.16, 'B': 493.88
        }
        self.ALL_NOTES = list(self.NOTE_FREQUENCIES.keys())
        self.MAJOR_INTERVALS = [0, 2, 4, 5, 7, 9, 11]
        self.MINOR_INTERVALS = [0, 2, 3, 5, 7, 8, 10]
        self.CUSTOM_INTERVALS = [0, 2, 4, 6, 7, 9, 11]
        self.PHRYGIAN_DOMINANT_INTERVALS = [0, 1, 4, 5, 7, 8, 10]
        self.HARMONIC_MINOR_INTERVALS = [0, 2, 3, 5, 7, 8, 11]
        self.MELODIC_MINOR_INTERVALS = [0, 2, 3, 5, 7, 9, 11]
        self.PENTATONIC_MAJOR_INTERVALS = [0, 2, 4, 7, 9]
        self.PENTATONIC_MINOR_INTERVALS = [0, 3, 5, 7, 10]

        self.POLYRHYTHM_PATTERNS = {
            '3:2': [2/3, 2/3, 2/3], 
            '3:4': [4/3, 4/3, 4/3], 
            '2:3': [1.5, 1.5],       
        }

        self.MUSICAL_SCALES = {}
        for note, base_freq in self.NOTE_FREQUENCIES.items():
            self.MUSICAL_SCALES[f"{note} Major"] = [base_freq * (2**(interval/12)) for interval in self.MAJOR_INTERVALS]
            self.MUSICAL_SCALES[f"{note} Minor"] = [base_freq * (2**(interval/12)) for interval in self.MINOR_INTERVALS]
            self.MUSICAL_SCALES[f"{note} Custom"] = [base_freq * (2**(interval/12)) for interval in self.CUSTOM_INTERVALS]
            self.MUSICAL_SCALES[f"{note} Phrygian Dominant"] = [base_freq * (2**(interval/12)) for interval in self.PHRYGIAN_DOMINANT_INTERVALS]
            self.MUSICAL_SCALES[f"{note} Harmonic Minor"] = [base_freq * (2**(interval/12)) for interval in self.HARMONIC_MINOR_INTERVALS]
            self.MUSICAL_SCALES[f"{note} Melodic Minor"] = [base_freq * (2**(interval/12)) for interval in self.MELODIC_MINOR_INTERVALS]
            self.MUSICAL_SCALES[f"{note} Pentatonic Major"] = [base_freq * (2**(interval/12)) for interval in self.PENTATONIC_MAJOR_INTERVALS]
            self.MUSICAL_SCALES[f"{note} Pentatonic Minor"] = [base_freq * (2**(interval/12)) for interval in self.PENTATONIC_MINOR_INTERVALS]

        self.DIATONIC_CHORDS = {
            'Major': {'I': [0, 2, 4], 'ii': [1, 3, 5], 'iii': [2, 4, 6], 'IV': [3, 5, 7], 'V': [4, 6, 8], 'vi': [5, 7, 9], 'vii°': [6, 8, 10]},
            'Minor': {'i': [0, 2, 4], 'ii°': [1, 3, 5], 'III': [2, 4, 6], 'iv': [3, 5, 7], 'v': [4, 6, 8], 'VI': [5, 7, 9], 'VII': [6, 8, 10]},
            'Custom': {'i': [0, 2, 4], 'II': [1, 3, 5], 'iii': [2, 4, 6], 'IV+': [3, 5, 7], 'V': [4, 6, 8], 'vi': [5, 7, 9], 'vii': [6, 8, 10]},
            'Phrygian Dominant': {'i': [0, 2, 4], 'II': [1, 3, 5], 'iii': [2, 4, 6], 'iv': [3, 5, 7], 'V': [4, 6, 8], 'VI': [5, 7, 9], 'vii': [6, 8, 10]},
            'Harmonic Minor': {'i': [0, 2, 4], 'ii°': [1, 3, 5], 'III+': [2, 4, 6], 'iv': [3, 5, 7], 'V': [4, 6, 8], 'VI': [5, 7, 9], 'vii°': [6, 8, 10]},
            'Melodic Minor': {'i': [0, 2, 4], 'ii': [1, 3, 5], 'III+': [2, 4, 6], 'IV': [3, 5, 7], 'V': [4, 6, 8], 'vi°': [5, 7, 9], 'vii°': [6, 8, 10]},
            'Pentatonic Major': {'I': [0, 2, 4], 'ii': [1, 3, 5], 'vi': [2, 4, 6]},
            'Pentatonic Minor': {'i': [0, 2, 4], 'IV': [1, 3, 5], 'v': [2, 4, 6]}
        }
        
        self.CHORD_PROGRESSIONS = {
            'Major': {'intro': ['I', 'IV'], 'verse': ['I', 'vi', 'IV', 'V'], 'pre-chorus': ['ii', 'IV', 'V'], 'chorus': ['I', 'V', 'vi', 'IV'], 'bridge': ['vi', 'V', 'IV', 'IV']},
            'Minor': {'intro': ['i', 'VI'], 'verse': ['i', 'VI', 'iv', 'v'], 'pre-chorus': ['ii°', 'VI', 'v'], 'chorus': ['i', 'v', 'VI', 'iv'], 'bridge': ['VI', 'VII', 'i', 'i']},
            'Custom': {'intro': ['i', 'IV+'], 'verse': ['i', 'vi', 'ii', 'V'], 'pre-chorus': ['II', 'V'], 'chorus': ['i', 'V', 'vi', 'IV+'], 'bridge': ['vi', 'V', 'IV+', 'IV+']},
            'Phrygian Dominant': {'intro': ['i', 'VI'], 'verse': ['i', 'II', 'VI', 'V'], 'pre-chorus': ['iv', 'V'], 'chorus': ['i', 'VI', 'V', 'i'], 'bridge': ['II', 'V', 'i', 'i']},
            'Harmonic Minor': {'intro': ['i', 'iv'], 'verse': ['i', 'V', 'i', 'VI'], 'pre-chorus': ['ii°', 'V'], 'chorus': ['i', 'VI', 'V'], 'bridge': ['VI', 'V', 'III+']},
            'Melodic Minor': {'intro': ['i', 'IV'], 'verse': ['i', 'V', 'i', 'vi°'], 'pre-chorus': ['IV', 'V'], 'chorus': ['i', 'vi°', 'V'], 'bridge': ['IV', 'V', 'III+']},
            'Pentatonic Major': {'intro': ['I'], 'verse': ['I', 'vi', 'I'], 'pre-chorus': ['ii'], 'chorus': ['I', 'vi', 'ii'], 'bridge': ['vi', 'ii', 'I']},
            'Pentatonic Minor': {'intro': ['i'], 'verse': ['i', 'v', 'i'], 'pre-chorus': ['IV'], 'chorus': ['i', 'v', 'IV'], 'bridge': ['v', 'IV', 'i']}
        }
        
        self.DRUM_SOUND_PROPERTIES = {
            'kick': {'frequency': 60, 'decay_rate': 15, 'waveform': 'sine', 'midi_note': 36},
            'snare': {'frequency': 200, 'decay_rate': 10, 'waveform': 'noise', 'midi_note': 38},
            'hihat': {'frequency': 8000, 'decay_rate': 20, 'waveform': 'noise', 'midi_note': 42}
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
            self.waveform_var.trace("w", self._save_settings)

    def _setup_ui(self):
        style = ttk.Style(); style.theme_use('clam'); style.configure("TScale", background="#2e2e2e", troughcolor="#444444")
        frame = tk.Frame(self.master, padx=10, pady=10, bg='#2e2e2e'); frame.pack(fill=tk.BOTH, expand=True)

        input_frame = tk.Frame(frame, bg='#2e2e2e'); input_frame.pack(pady=5, fill=tk.X)
        tk.Label(input_frame, text="Duration (s):", bg='#2e2e2e', fg='white').pack(side=tk.LEFT, padx=5)
        self.entry_duration = tk.Entry(input_frame, bg='#444444', fg='white', width=10); self.entry_duration.pack(side=tk.LEFT, padx=5)
        
        self.scale_var = tk.StringVar(self.master)
        
        self.bit_depth_var = tk.StringVar(self.master)
        tk.Label(input_frame, text="Bit Depth:", bg='#2e2e2e', fg='white').pack(side=tk.LEFT, padx=5)
        self.bit_depth_menu = tk.OptionMenu(input_frame, self.bit_depth_var, "8", "16")
        self.bit_depth_menu.pack(side=tk.LEFT, padx=5)
        
        self.waveform_var = tk.StringVar(self.master)
        tk.Label(input_frame, text="Waveform:", bg='#2e2e2e', fg='white').pack(side=tk.LEFT, padx=5)
        self.waveform_menu = tk.OptionMenu(input_frame, self.waveform_var, "Sine", "Square", "Sawtooth", "Triangle", "Piano")
        self.waveform_menu.pack(side=tk.LEFT, padx=5)
        
        self.debug_button = tk.Button(input_frame, text="Debug", command=self.open_debug_window, bg='#4d6b88', fg='white'); self.debug_button.pack(side=tk.RIGHT, padx=5)

        buttons_frame = tk.Frame(frame, bg='#2e2e2e'); buttons_frame.pack(pady=5, fill=tk.X)
        
        left_buttons_frame = tk.Frame(buttons_frame, bg='#2e2e2e')
        left_buttons_frame.pack(side=tk.LEFT)

        self.play_button = tk.Button(left_buttons_frame, text="Play", command=self.start_music, bg='#555555', fg='white'); self.play_button.pack(side=tk.LEFT, padx=5)
        self.replay_button = tk.Button(left_buttons_frame, text="Replay", command=self.replay_music, bg='#555555', fg='white', state=tk.DISABLED); self.replay_button.pack(side=tk.LEFT, padx=5)
        self.stop_button = tk.Button(left_buttons_frame, text="Stop", command=self.stop_music, bg='#555555', fg='white', state=tk.DISABLED); self.stop_button.pack(side=tk.LEFT, padx=5)
        self.loop_var = BooleanVar()
        self.loop_check = tk.Checkbutton(left_buttons_frame, text="Loop", variable=self.loop_var, bg='#2e2e2e', fg='white', selectcolor='#444444', command=self._save_settings); self.loop_check.pack(side=tk.LEFT, padx=10)
        self.scales_button = tk.Button(left_buttons_frame, text="Scales", command=self._open_scales_window, bg='#4d6b88', fg='white'); self.scales_button.pack(side=tk.LEFT, padx=5)

        right_options_frame = tk.Frame(buttons_frame, bg='#2e2e2e')
        right_options_frame.pack(side=tk.RIGHT, padx=10)

        self.polyphonic_var = BooleanVar()
        self.polyrhythmic_var = BooleanVar()
        self.polytonal_var = BooleanVar()
        self.force_var = BooleanVar()

        tk.Checkbutton(right_options_frame, text="Polyphonic", variable=self.polyphonic_var, bg='#2e2e2e', fg='white', selectcolor='#444444', command=self._save_settings).pack(side=tk.LEFT)
        tk.Checkbutton(right_options_frame, text="Polyrhythmic", variable=self.polyrhythmic_var, bg='#2e2e2e', fg='white', selectcolor='#444444', command=self._save_settings).pack(side=tk.LEFT)
        tk.Checkbutton(right_options_frame, text="Polytonal", variable=self.polytonal_var, bg='#2e2e2e', fg='white', selectcolor='#444444', command=self._save_settings).pack(side=tk.LEFT)
        tk.Checkbutton(right_options_frame, text="Force", variable=self.force_var, bg='#2e2e2e', fg='white', selectcolor='#444444', command=self._save_settings).pack(side=tk.LEFT, padx=(10,0))

        volume_frame = tk.Frame(frame, bg='#2e2e2e'); volume_frame.pack(pady=5, fill=tk.X)
        tk.Label(volume_frame, text="Harmonic Vol:", bg='#2e2e2e', fg='white').pack(side=tk.LEFT, padx=5)
        self.melody_volume_slider = ttk.Scale(volume_frame, from_=0, to=100, orient=tk.HORIZONTAL, command=self._update_and_save_melody_volume); self.melody_volume_slider.pack(side=tk.LEFT, fill=tk.X, expand=True)
        tk.Label(volume_frame, text="Drum Volume:", bg='#2e2e2e', fg='white').pack(side=tk.LEFT, padx=5)
        self.drum_volume_slider = ttk.Scale(volume_frame, from_=0, to=100, orient=tk.HORIZONTAL, command=self._update_and_save_drum_volume); self.drum_volume_slider.pack(side=tk.LEFT, fill=tk.X, expand=True)

        log_frame = tk.Frame(frame, bg='#2e2e2e'); log_frame.pack(pady=5, fill=tk.X)
        tk.Label(log_frame, text="Main Events Log", bg='#2e2e2e', fg='white').pack()
        self.main_log_area = scrolledtext.ScrolledText(log_frame, wrap=tk.WORD, height=6, state='disabled', bg='black', fg='white'); self.main_log_area.pack(fill=tk.X)
        self.main_log_area.tag_config('main', foreground='lightblue')
        
        harmonic_logs_frame = tk.Frame(frame, bg='#2e2e2e'); harmonic_logs_frame.pack(pady=5, fill=tk.BOTH, expand=True)
        
        harmonic_logs_frame.grid_columnconfigure(0, weight=1); harmonic_logs_frame.grid_columnconfigure(1, weight=1)
        harmonic_logs_frame.grid_rowconfigure(0, weight=1); harmonic_logs_frame.grid_rowconfigure(1, weight=1)

        melody1_log_frame = tk.Frame(harmonic_logs_frame, bg='#2e2e2e'); melody1_log_frame.grid(row=0, column=0, sticky='nsew', padx=1, pady=2)
        tk.Label(melody1_log_frame, text="Melody 1 Log", bg='#2e2e2e', fg='white').pack()
        self.melody1_log_area = scrolledtext.ScrolledText(melody1_log_frame, wrap=tk.WORD, height=5, state='disabled', bg='black', fg='lightgreen'); self.melody1_log_area.pack(fill=tk.BOTH, expand=True)
        self.melody1_log_area.tag_config('melody1', foreground='lightgreen')

        melody2_log_frame = tk.Frame(harmonic_logs_frame, bg='#2e2e2e'); melody2_log_frame.grid(row=1, column=0, sticky='nsew', padx=1, pady=2)
        tk.Label(melody2_log_frame, text="Melody 2 Log", bg='#2e2e2e', fg='white').pack()
        self.melody2_log_area = scrolledtext.ScrolledText(melody2_log_frame, wrap=tk.WORD, height=5, state='disabled', bg='black', fg='#98FB98'); self.melody2_log_area.pack(fill=tk.BOTH, expand=True)
        self.melody2_log_area.tag_config('melody2', foreground='#98FB98')

        bass_log_frame = tk.Frame(harmonic_logs_frame, bg='#2e2e2e'); bass_log_frame.grid(row=0, column=1, sticky='nsew', padx=1, pady=2)
        tk.Label(bass_log_frame, text="Bass Log", bg='#2e2e2e', fg='white').pack()
        self.bass_log_area = scrolledtext.ScrolledText(bass_log_frame, wrap=tk.WORD, height=5, state='disabled', bg='black', fg='#FFC0CB'); self.bass_log_area.pack(fill=tk.BOTH, expand=True)
        self.bass_log_area.tag_config('bass', foreground='#FFC0CB')

        chord_log_frame = tk.Frame(harmonic_logs_frame, bg='#2e2e2e'); chord_log_frame.grid(row=1, column=1, sticky='nsew', padx=1, pady=2)
        tk.Label(chord_log_frame, text="Chord Log", bg='#2e2e2e', fg='white').pack()
        self.chord_log_area = scrolledtext.ScrolledText(chord_log_frame, wrap=tk.WORD, height=5, state='disabled', bg='black', fg='#ADD8E6'); self.chord_log_area.pack(fill=tk.BOTH, expand=True)
        self.chord_log_area.tag_config('chords', foreground='#ADD8E6')

        drum_log_frame = tk.Frame(frame, bg='#2e2e2e'); drum_log_frame.pack(pady=5, fill=tk.X)
        tk.Label(drum_log_frame, text="Drum Events Log", bg='#2e2e2e', fg='white').pack()
        self.drum_log_area = scrolledtext.ScrolledText(drum_log_frame, wrap=tk.WORD, height=6, state='disabled', bg='black', fg='orange'); self.drum_log_area.pack(fill=tk.X)
        self.drum_log_area.tag_config('drums', foreground='orange')

        export_frame = tk.Frame(frame, bg='#2e2e2e'); export_frame.pack(pady=10, fill=tk.X)
        self.export_wav_button = tk.Button(export_frame, text="Export WAV", command=self.export_wav_file, bg='#555555', fg='white', state=tk.DISABLED); self.export_wav_button.pack(side=tk.LEFT, padx=5)
        self.export_midi_button = tk.Button(export_frame, text="Export MIDI", command=self.export_midi_file, bg='#555555', fg='white', state=tk.DISABLED); self.export_midi_button.pack(side=tk.LEFT, padx=5)
        
        self.reload_button = tk.Button(export_frame, text="Reload Script", command=self.reload_script, bg='#884d4d', fg='white'); self.reload_button.pack(side=tk.RIGHT, padx=5)

    def _save_settings(self, *args):
        settings = {
            "duration": self.entry_duration.get(),
            "bit_depth": self.bit_depth_var.get(),
            "waveform": self.waveform_var.get(),
            "loop": self.loop_var.get(),
            "polyphonic": self.polyphonic_var.get(),
            "polyrhythmic": self.polyrhythmic_var.get(),
            "polytonal": self.polytonal_var.get(),
            "force": self.force_var.get(),
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
        if self.ui_mode:
            try:
                if os.path.exists(self.SETTINGS_FILE):
                    with open(self.SETTINGS_FILE, 'r') as f:
                        settings = json.load(f)
                else:
                    settings = {} # Use defaults if file doesn't exist

                self.entry_duration.delete(0, tk.END)
                self.entry_duration.insert(0, settings.get("duration", "30"))
                self.bit_depth_var.set(settings.get("bit_depth", "16"))
                self.waveform_var.set(settings.get("waveform", "Sine"))
                self.loop_var.set(settings.get("loop", False))
                self.polyphonic_var.set(settings.get("polyphonic", True))
                self.polyrhythmic_var.set(settings.get("polyrhythmic", True))
                self.polytonal_var.set(settings.get("polytonal", True))
                self.force_var.set(settings.get("force", False))
                self.melody_volume_slider.set(settings.get("harmonic_vol", 70.0))
                self.drum_volume_slider.set(settings.get("drum_vol", 70.0))
                
                loaded_scales = settings.get("scales", {})
                for st, var in self.scale_vars.items():
                    var.set(loaded_scales.get(st, True))

            except Exception as e:
                self.update_log(f"Error loading settings: {e}", 'main')
        else:
            # For no-ui mode, ignore the settings file and use hardcoded defaults.
            self.settings = {
                "duration": "90",
                "bit_depth": "16",
                "waveform": "Piano",
                "polyphonic": True,
                "polyrhythmic": True,
                "polytonal": True,
                "force": False
            }
            self.scale_vars = {st: True for st in self.scale_types}
            self.settings["scales"] = self.scale_vars

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

    def _get_related_key(self, base_key_name):
        base_note, scale_kind = base_key_name.split(' ', 1)
        base_note_index = self.ALL_NOTES.index(base_note)
        
        options = []
        # Dominant
        dominant_index = (base_note_index + 7) % 12
        options.append(f"{self.ALL_NOTES[dominant_index]} {scale_kind}")
        # Relative Major/Minor
        if 'Major' in scale_kind:
            relative_minor_index = (base_note_index - 3) % 12
            options.append(f"{self.ALL_NOTES[relative_minor_index]} Minor")
        elif 'Minor' in scale_kind:
            relative_major_index = (base_note_index + 3) % 12
            options.append(f"{self.ALL_NOTES[relative_major_index]} Major")
            
        return random.choice(options)

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
    
    def _generate_rhythmic_pattern(self, section_name):
        kick_probability = 0.8 if section_name in ['intro', 'verse'] else 0.95
        snare_probability = 0.5 if section_name in ['verse', 'chorus'] else 0.2
        hihat_probability = 0.7 if section_name in ['pre-chorus', 'chorus'] else 0.4
        
        pattern = []
        if random.random() < kick_probability: pattern.append((0, 'kick'))
        if random.random() < snare_probability: pattern.append((1, 'snare'))
        if random.random() < kick_probability: pattern.append((2, 'kick'))
        if random.random() < snare_probability: pattern.append((3, 'snare'))
        
        if random.random() < hihat_probability: pattern.append((0.5, 'hihat'))
        if random.random() < hihat_probability: pattern.append((1.5, 'hihat'))
        if random.random() < hihat_probability: pattern.append((2.5, 'hihat'))
        if random.random() < hihat_probability: pattern.append((3.5, 'hihat'))
        
        if random.random() < 0.2: pattern.append((random.choice([0.25, 0.75, 1.25, 1.75, 2.25, 2.75, 3.25, 3.75]), random.choice(['kick', 'snare', 'hihat'])))
        
        return sorted(pattern)

    def _generate_melodic_note(self, current_note_index, last_note_index, last_last_note_idx, scale_notes, current_chord_indices, last_direction, consecutive_steps, section_type, scale_type, log_callback, motion_type=None, counter_melody_direction=None, octave_center_idx=None, is_strong_beat=False):
        scale_length = len(scale_notes)
        base_scale_len = 7 if 'Pentatonic' not in scale_type else 5
        next_note_index = current_note_index
        next_direction = last_direction
        consecutive_steps_new = consecutive_steps
        rule_applied = "No rule"

        if motion_type and counter_melody_direction is not None:
            if motion_type == 'contrary' and counter_melody_direction != 0:
                next_direction = -counter_melody_direction; next_note_index = (current_note_index + next_direction); rule_applied = "Contrary Motion"
            elif motion_type == 'oblique':
                next_direction = 0; next_note_index = current_note_index; rule_applied = "Oblique Motion"
            elif motion_type == 'similar' and counter_melody_direction != 0:
                next_direction = counter_melody_direction; next_note_index = (current_note_index + next_direction); rule_applied = "Similar Motion"
        
        if rule_applied == "No rule" and is_strong_beat and random.random() < 0.9:
            if current_chord_indices:
                closest_chord_tone = min(current_chord_indices, key=lambda x: abs(x - current_note_index))
                next_note_index = closest_chord_tone; rule_applied = "Strong Beat Chord Tone"

        if rule_applied == "No rule" and last_note_index is not None and abs(current_note_index - last_note_index) > 2:
            if random.random() < 0.9:
                next_direction = -np.sign(current_note_index - last_note_index); next_note_index = (current_note_index + next_direction); consecutive_steps_new = 1; rule_applied = "Leap Recovery"

        if rule_applied == "No rule" and last_last_note_idx is not None and last_note_index is not None and abs(current_note_index - last_note_index) > 2 and abs(last_note_index - last_last_note_idx) > 2:
            is_triad = False; all_notes = sorted([last_last_note_idx, last_note_index, current_note_index])
            for _, intervals in self.DIATONIC_CHORDS.get(scale_type, {}).items():
                chord_degrees = [(all_notes[0] % base_scale_len) + i for i in intervals]
                if all((note % base_scale_len) in chord_degrees for note in all_notes): is_triad = True; break
            if not is_triad:
                next_direction = -np.sign(current_note_index - last_note_index) if np.sign(current_note_index - last_note_index) == np.sign(last_note_index - last_last_note_idx) else last_direction
                next_note_index = (current_note_index + next_direction); consecutive_steps_new = 1; rule_applied = "Arpeggio Break"
            elif random.random() < 0.6:
                next_direction = -np.sign(current_note_index - last_note_index); next_note_index = (current_note_index + next_direction); consecutive_steps_new = 1; rule_applied = "Arpeggio Continuation"

        if rule_applied == "No rule" and base_scale_len == 7:
            current_degree = current_note_index % base_scale_len
            if current_degree == 6 and random.random() < 0.9:
                next_note_index, next_direction, consecutive_steps_new, rule_applied = current_note_index + 1, 1, 1, "Tritone Resolution (7->1)"
            elif current_degree == 3 and random.random() < 0.8:
                next_note_index, next_direction, consecutive_steps_new, rule_applied = current_note_index - 1, -1, 1, "Tritone Resolution (4->3)"

        if rule_applied == "No rule" and last_note_index is not None and abs(current_note_index - last_note_index) > 3 and random.random() < 0.8:
            next_direction = -np.sign(current_note_index - last_note_index); next_note_index = (current_note_index + next_direction); consecutive_steps_new = 1; rule_applied = "Large Leap Recovery"

        if rule_applied == "No rule" and consecutive_steps >= 4:
            next_direction = -last_direction if last_direction != 0 else random.choice([-1, 1]); next_note_index = (current_note_index + next_direction); consecutive_steps_new = 1; rule_applied = "Step Sequence Break"
            
        if rule_applied == "No rule" and octave_center_idx is not None:
            distance_from_center = current_note_index - octave_center_idx
            if abs(distance_from_center) > 4 and random.random() < 0.3:
                next_direction = -np.sign(distance_from_center); next_note_index = (current_note_index + next_direction); consecutive_steps_new = 1; rule_applied = "Return to Center"
        
        if rule_applied == "No rule":
            is_chord_tone = (current_note_index % base_scale_len) in [idx % base_scale_len for idx in current_chord_indices]
            if not is_chord_tone and random.random() < 0.75:
                next_direction = random.choice([-1, 1]); next_note_index = current_note_index + next_direction; consecutive_steps_new = 1; rule_applied = "Non-Chord Tone Resolution"
            else:
                if random.random() < 0.7:
                    if random.random() < 0.7 and last_direction is not None and consecutive_steps < 4:
                        next_direction, consecutive_steps_new = last_direction, consecutive_steps + 1
                    else:
                        next_direction, consecutive_steps_new = random.choice([-1, 1]), 0
                    next_note_index = (current_note_index + next_direction); rule_applied = "Default Step"
                else:
                    jump = random.choice([-5, -4, -2, 2, 4, 5]); next_note_index, next_direction, consecutive_steps_new = (current_note_index + jump), np.sign(jump), 0; rule_applied = "Default Leap"
        
        log_callback(f"    Rule Applied: {rule_applied}", 'debug', debug_only=True)
        next_note_index = max(0, min(scale_length - 1, next_note_index))
        return next_note_index, next_direction, consecutive_steps_new

    def _generate_bass_line_note(self, current_chord_indices): return current_chord_indices[0] if random.random() < 0.8 else random.choice(current_chord_indices[1:3])

    def _generate_tone(self, duration_sec, sample_rate, freqs, waveform_type):
        if not isinstance(freqs, list): freqs = [freqs]
        num_samples = int(duration_sec * sample_rate)
        t = np.linspace(0, duration_sec, num_samples, False)
        
        combined_audio = np.zeros(num_samples)
        if not freqs: return combined_audio

        for frequency in freqs:
            if waveform_type == 'Square': audio_data = np.sign(np.sin(frequency * t * 2 * np.pi))
            elif waveform_type == 'Sawtooth': audio_data = signal.sawtooth(2 * np.pi * frequency * t)
            elif waveform_type == 'Triangle': audio_data = signal.sawtooth(2 * np.pi * frequency * t, width=0.5)
            elif waveform_type == 'Piano':
                fundamental = np.sin(frequency * t * 2 * np.pi)
                second_harmonic = 0.5 * np.sin(frequency * 2 * t * 2 * np.pi)
                third_harmonic = 0.25 * np.sin(frequency * 3 * t * 2 * np.pi)
                decay_envelope = np.exp(-2.0 * t)
                audio_data = (fundamental + second_harmonic + third_harmonic) * decay_envelope
            else: # Sine wave
                audio_data = np.sin(frequency * t * 2 * np.pi)
            combined_audio += audio_data

        return combined_audio / len(freqs) if freqs else np.zeros(num_samples)


    def _generate_percussion_sound(self, drum_type, duration_sec, sample_rate):
        properties = self.DRUM_SOUND_PROPERTIES.get(drum_type)
        num_samples = int(duration_sec * sample_rate)
        t = np.linspace(0, duration_sec, num_samples, False)
        if properties['waveform'] == 'sine': audio_data = np.sin(properties['frequency'] * t * 2 * np.pi)
        else:
            audio_data = np.random.uniform(-1, 1, num_samples)
            if drum_type == 'hihat': b, a = signal.butter(10, 5000 / (0.5 * sample_rate), btype='high'); audio_data = signal.lfilter(b, a, audio_data)
        return audio_data * np.exp(-properties['decay_rate'] * t)

    def _generate_dynamic_drum_rhythm(self, section_name, section_duration, drum_bpm, melody_rhythm_data):
        drum_track_data, beat_duration = [], 60.0 / drum_bpm
        
        selected_pattern = self._generate_rhythmic_pattern(section_name)
        
        current_time = 0.0
        while current_time < section_duration:
            for beat, drum_type in selected_pattern:
                hit_time = current_time + (beat * beat_duration)
                if hit_time < section_duration: drum_track_data.append({'start_time': hit_time, 'duration': beat_duration * 0.25, 'drum_type': drum_type})
            current_time += beat_duration * 4

        melody_accent_chance = 0.3
        syncopation_chance = 0.25
        
        for note in melody_rhythm_data:
            if random.random() < melody_accent_chance:
                 drum_track_data.append({'start_time': note['start_time'], 'duration': beat_duration * 0.25, 'drum_type': 'kick'})
            
            if random.random() < syncopation_chance and note['start_time'] > beat_duration * 0.5:
                syncopated_time = note['start_time'] - (beat_duration / 2)
                drum_track_data.append({'start_time': syncopated_time, 'duration': beat_duration * 0.25, 'drum_type': random.choice(['hihat', 'snare'])})

        unique_hits = sorted(list(set((d['start_time'], d['drum_type'], d['duration']) for d in drum_track_data)))
        drum_track_data = [{'start_time': t, 'drum_type': dt, 'duration': dur} for t, dt, dur in unique_hits]

        return drum_track_data
    
    def _get_rhythm_sequence(self, total_beats, polyrhythm_pattern=None, is_active=True):
        sequence = []
        if not is_active:
            remaining_beats = total_beats
            while remaining_beats > 0:
                note_length = random.choice([4.0, 2.0, 2.0]) if remaining_beats >= 4.0 else remaining_beats
                if note_length > remaining_beats: note_length = remaining_beats
                sequence.append(note_length)
                remaining_beats -= note_length
            return sequence

        if polyrhythm_pattern:
            pattern_duration = sum(polyrhythm_pattern)
            num_patterns = math.ceil(total_beats / pattern_duration)
            full_pattern = polyrhythm_pattern * num_patterns
            
            current_beats = 0
            for note_len in full_pattern:
                if current_beats + note_len > total_beats:
                    sequence.append(total_beats - current_beats)
                    break
                sequence.append(note_len)
                current_beats += note_len
        else: # Standard active rhythm
            remaining_beats = total_beats
            while remaining_beats > 0:
                note_length = random.choice([0.5, 1.0, 1.5, 2.0]) if remaining_beats >= 2.0 else random.choice([0.5, 1.0])
                if note_length > remaining_beats: note_length = remaining_beats
                sequence.append(note_length)
                remaining_beats -= note_length
        return sequence

    def _generate_song_section_data(self, selected_scale_name, selected_scale_notes, scale_type, progression_name, section_duration, melody_bpm, log_callback, scale_notes_base):
        progression_romans = self.CHORD_PROGRESSIONS.get(scale_type, {}).get(progression_name, [])
        log_callback(f"Progression for {progression_name.title()}: {progression_romans}", 'main')

        if not progression_romans:
            progression_romans = ['i', 'iv', 'v', 'i'] if 'Minor' in scale_type else ['I', 'IV', 'V', 'I']
        
        chord_progression_indices = [self.DIATONIC_CHORDS[scale_type].get(r, []) for r in progression_romans]
        
        melody1_events, melody2_events, bass_events, chord_events = [], [], [], []
        
        base_scale_len = len(scale_notes_base)
        m1_octave_center = base_scale_len * 2 + (base_scale_len // 2)
        m2_octave_center = base_scale_len + (base_scale_len // 2)
        
        initial_chord_note_m1 = chord_progression_indices[0][0] if chord_progression_indices and chord_progression_indices[0] else 0
        initial_chord_note_m2 = chord_progression_indices[0][-1] if chord_progression_indices and chord_progression_indices[0] else 0
        
        m1_last_idx = initial_chord_note_m1 + base_scale_len * 2
        m1_current_idx = m1_last_idx
        m1_last_last_idx = None
        m1_last_direction, m1_consecutive_steps = 0, 0
        
        m2_last_idx = initial_chord_note_m2 + base_scale_len
        m2_current_idx = m2_last_idx
        m2_last_last_idx = None
        m2_last_direction, m2_consecutive_steps = 0, 0
        
        beat_duration = 60.0 / melody_bpm
        chord_duration = section_duration / len(chord_progression_indices) if chord_progression_indices else section_duration
        
        if self.ui_mode:
            force_check = self.force_var.get()
            polyphonic_check = self.polyphonic_var.get()
            polyrhythmic_check = self.polyrhythmic_var.get()
            polytonal_check = self.polytonal_var.get()
        else:
            force_check = self.settings.get("force", False)
            polyphonic_check = self.settings.get("polyphonic", True)
            polyrhythmic_check = self.settings.get("polyrhythmic", True)
            polytonal_check = self.settings.get("polytonal", True)

        if force_check:
            is_polyphonic = polyphonic_check
            is_polyrhythmic = polyrhythmic_check
            is_polytonal = polytonal_check
        else:
            is_polyphonic = polyphonic_check and (random.random() < 0.6)
            is_polyrhythmic = polyrhythmic_check and (random.random() < 0.3)
            is_polytonal = polytonal_check and (random.random() < 0.4)

        scale_notes_m1 = selected_scale_notes
        scale_notes_m2 = selected_scale_notes
        scale_type_m2 = scale_type

        log_callback(f"Polyphonic: {is_polyphonic}, Polyrhythmic: {is_polyrhythmic}, Polytonal: {is_polytonal}", 'main')

        if is_polytonal:
            related_key = self._get_related_key(selected_scale_name)
            scale_notes_m2_base = self.MUSICAL_SCALES[related_key]
            scale_notes_m2 = [f/2 for f in scale_notes_m2_base] + scale_notes_m2_base + [f*2 for f in scale_notes_m2_base]
            scale_type_m2 = related_key.split(' ', 1)[1]
            log_callback(f"Melody 2 is in a different key: {related_key}", 'main')

        current_time = 0.0
        last_chord_indices = []
        
        melodic_focus = 1
        focus_switch_chance = 0.4

        for i, chord_indices in enumerate(chord_progression_indices):
            if not chord_indices: continue

            if random.random() < focus_switch_chance:
                melodic_focus = 2 if melodic_focus == 1 else 1
                log_callback(f"Melodic focus switched to Melody {melodic_focus}", 'main')
            
            chord_freqs = [selected_scale_notes[i] for i in chord_indices]
            num_chord_beats = int(round(chord_duration / beat_duration))
            polyrhythm_pattern = self.POLYRHYTHM_PATTERNS[random.choice(list(self.POLYRHYTHM_PATTERNS.keys()))] if is_polyrhythmic else None
            
            rhythm_sequence_m1 = self._get_rhythm_sequence(num_chord_beats, polyrhythm_pattern, is_active=(melodic_focus==1))
            rhythm_sequence_m2 = self._get_rhythm_sequence(num_chord_beats, polyrhythm_pattern if random.random() > 0.5 else None, is_active=(melodic_focus==2))

            time_m1, time_m2 = current_time, current_time
            
            is_first_note_in_chord = True
            
            log_callback(f"Generating chord {i+1}/{len(chord_progression_indices)}. M1 beats: {len(rhythm_sequence_m1)}, M2 beats: {len(rhythm_sequence_m2)}", 'debug', debug_only=True)
            
            while rhythm_sequence_m1 or rhythm_sequence_m2:
                motion_type = self._get_contrapuntal_motion(m1_last_direction)
                
                can_play_m1 = bool(rhythm_sequence_m1)
                can_play_m2 = bool(rhythm_sequence_m2)

                if can_play_m1 and (not can_play_m2 or time_m1 <= time_m2):
                    beat = rhythm_sequence_m1.pop(0)
                    duration = beat * beat_duration
                    log_callback(f"  M1: Processing beat. Remaining: {len(rhythm_sequence_m1)}", 'debug', debug_only=True)
                    
                    m1_new_idx, m1_last_direction, m1_consecutive_steps = self._generate_melodic_note(m1_current_idx, m1_last_idx, m1_last_last_idx, scale_notes_m1, chord_indices, m1_last_direction, m1_consecutive_steps, progression_name, scale_type, log_callback, octave_center_idx=m1_octave_center, is_strong_beat=is_first_note_in_chord)
                    melody1_notes = [scale_notes_m1[m1_new_idx]]

                    if progression_name == 'chorus' and random.random() < 0.35:
                        harmony_note_index = m1_new_idx + 2
                        melody_degree = m1_new_idx % base_scale_len
                        harmony_degree = harmony_note_index % base_scale_len
                        chord_degrees = [idx % base_scale_len for idx in chord_indices]
                        
                        if harmony_degree in chord_degrees and harmony_note_index < len(scale_notes_m1):
                            melody1_notes.append(scale_notes_m1[harmony_note_index])

                    melody1_events.append({'start_time': time_m1, 'duration': duration, 'freqs': melody1_notes, 'scale_idx': m1_new_idx})
                    m1_last_last_idx, m1_last_idx, m1_current_idx = m1_last_idx, m1_current_idx, m1_new_idx
                    time_m1 += duration

                elif can_play_m2:
                    beat = rhythm_sequence_m2.pop(0)
                    duration = beat * beat_duration
                    log_callback(f"  M2: Processing beat. Remaining: {len(rhythm_sequence_m2)}", 'debug', debug_only=True)

                    for _ in range(5):
                        m2_new_idx, m2_last_direction, m2_consecutive_steps = self._generate_melodic_note(m2_current_idx, m2_last_idx, m2_last_last_idx, scale_notes_m2, chord_indices, m2_last_direction, m2_consecutive_steps, progression_name, scale_type_m2, log_callback, motion_type=motion_type, counter_melody_direction=m1_last_direction, octave_center_idx=m2_octave_center, is_strong_beat=is_first_note_in_chord)
                        
                        if is_polyphonic and melody1_events and melody2_events:
                            last_m1_note_idx = melody1_events[-1]['scale_idx']
                            last_m2_note_idx = melody2_events[-1]['scale_idx']
                            
                            dir_m1 = np.sign(m1_current_idx - last_m1_note_idx)
                            dir_m2 = np.sign(m2_new_idx - m2_current_idx)

                            if dir_m1 == dir_m2 and dir_m1 != 0:
                                interval_prev = abs(last_m1_note_idx - last_m2_note_idx) % base_scale_len
                                interval_new = abs(m1_current_idx - m2_new_idx) % base_scale_len
                                
                                is_parallel_fifth = interval_prev == 4 and interval_new == 4
                                is_parallel_octave = interval_prev == 0 and interval_new == 0

                                if is_parallel_fifth or is_parallel_octave:
                                    continue
                        break

                    melody2_events.append({'start_time': time_m2, 'duration': duration, 'freqs': [scale_notes_m2[m2_new_idx]], 'scale_idx': m2_new_idx})
                    m2_last_last_idx, m2_last_idx, m2_current_idx = m2_last_idx, m2_current_idx, m2_new_idx
                    time_m2 += duration
                
                else: 
                    log_callback("Melody generation loop breaking.", 'debug', debug_only=True)
                    break
                
                is_first_note_in_chord = False

            chord_rhythm = self._get_rhythm_sequence(num_chord_beats)
            chord_time = current_time
            for beat in chord_rhythm:
                duration = beat * beat_duration
                if chord_time >= current_time + chord_duration: break
                
                bass_note_index = self._generate_bass_line_note(chord_indices)
                bass_notes = [selected_scale_notes[bass_note_index] / 2]
                bass_events.append({'start_time': chord_time, 'duration': duration, 'freqs': bass_notes})
                
                chord_events.append({'start_time': chord_time, 'duration': duration, 'freqs': chord_freqs})
                chord_time += duration

            current_time += chord_duration
            last_chord_indices = chord_indices

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

    def _generate_full_song(self):
        if self.ui_mode:
            total_duration = int(self.entry_duration.get())
            bit_depth = int(self.bit_depth_var.get())
            waveform_type = self.waveform_var.get()
        else:
            total_duration = int(self.settings.get("duration", 90))
            bit_depth = int(self.settings.get("bit_depth", 16))
            waveform_type = self.settings.get("waveform", "Sine")

        melody_bpm = random.randint(90, 150)
        log_callback = self.update_log

        log_callback(f"Generating {total_duration}s of music...", 'main')
        
        if self.ui_mode:
            enabled_scale_types = [st for st, var in self.scale_vars.items() if var.get()]
        else:
            enabled_scale_types = [st for st, enabled in self.scale_vars.items() if enabled]

        if not enabled_scale_types:
            log_callback("No scales enabled! Defaulting to Major.", 'main')
            enabled_scale_types = ["Major"]

        possible_scales = [name for name in self.MUSICAL_SCALES.keys() if name.split(' ', 1)[1] in enabled_scale_types]
        if not possible_scales:
            log_callback("Error: No possible scales found. Defaulting to C Major.", 'main')
            selected_scale_name = "C Major"
        else:
            selected_scale_name = random.choice(possible_scales)

        if self.ui_mode:
            self.master.after(0, lambda: self.scale_var.set(selected_scale_name))
        
        scale_notes_base = self.MUSICAL_SCALES[selected_scale_name]
        scale_name_parts = selected_scale_name.split(' ')
        scale_type = ' '.join(scale_name_parts[1:])
        scale_notes = [f/2 for f in scale_notes_base] + scale_notes_base + [f*2 for f in scale_notes_base] + [f*4 for f in scale_notes_base]
        
        log_callback(f"Key: {selected_scale_name}, Tempo: {melody_bpm} BPM", 'main')
        
        ending_style_options = ['fade_out', 'tonic_cadence']
        if 'Minor' in scale_type: ending_style_options.append('picardy_third')
        ending_style = random.choice(ending_style_options)
        log_callback(f"Ending: {ending_style.replace('_', ' ').title()}", 'main')
        
        structure = ['intro', 'verse', 'chorus', 'verse', 'chorus', 'bridge', 'chorus'] if total_duration > 60 else \
                    ['chorus', 'verse', 'chorus'] if total_duration >= 45 else \
                    ['chorus', 'chorus'] if total_duration >= 30 else ['verse']

        cached_section_data, cached_drum_data = None, None
        section_duration = total_duration / len(structure)
        
        full_song_data = {'melody1': [], 'melody2': [], 'bass': [], 'chords': []}
        full_drum_data = []
        current_time = 0.0
        
        section_log_timeline = []

        for i, section_name in enumerate(structure):
            log_callback(f"--- Generating {section_name.title()} ---", 'main')
            
            section_log_timeline.append({'start_time': current_time, 'log_type': 'main', 'message': f"--- Playing {section_name.title()} ---"})

            if section_name == 'chorus' and cached_section_data is not None:
                section_data = copy.deepcopy(cached_section_data)
                drum_data = copy.deepcopy(cached_drum_data)
            else:
                section_data = self._generate_song_section_data(selected_scale_name, scale_notes, scale_type, section_name, section_duration, melody_bpm, log_callback, scale_notes_base)
                melody_rhythm_for_drums = [{'start_time': item['start_time']} for item in section_data['melody1']]
                drum_data = self._generate_dynamic_drum_rhythm(section_name, section_duration, melody_bpm, melody_rhythm_for_drums)
                
                if section_name == 'chorus':
                    cached_section_data = section_data
                    cached_drum_data = drum_data
            
            for part, events in section_data.items():
                for item in events:
                    item_copy = item.copy(); item_copy['start_time'] += current_time
                    full_song_data[part].append(item_copy)
            
            for item in drum_data:
                item_copy = item.copy(); item_copy['start_time'] += current_time
                full_drum_data.append(item_copy)

            current_time += section_duration

        self.last_song_data, self.last_drum_data, self.last_melody_bpm = full_song_data, full_drum_data, melody_bpm
        self.last_bit_depth, self.last_sample_rate = bit_depth, 44100

        return full_song_data, full_drum_data, section_log_timeline, ending_style, current_time

    def _music_generation_and_playback_thread(self, initial_melody_volume, initial_drum_volume, on_finish_callback):
        try:
            full_song_data, full_drum_data, section_log_timeline, ending_style, total_duration = self._generate_full_song()
            
            waveform_type = self.waveform_var.get()
            SAMPLE_RATE = self.last_sample_rate
            
            total_samples = int(total_duration * SAMPLE_RATE) + 10
            melody1_track, melody2_track, bass_track, chord_track, drum_track = (np.zeros(total_samples, dtype=np.float64) for _ in range(5))

            FADE_DURATION_S = 0.005
            fade_samples = int(FADE_DURATION_S * SAMPLE_RATE)

            track_map = {'melody1': melody1_track, 'melody2': melody2_track, 'bass': bass_track, 'chords': chord_track}
            for part_name, track in track_map.items():
                for item in full_song_data[part_name]:
                    segment = self._generate_tone(item['duration'], SAMPLE_RATE, item['freqs'], waveform_type)
                    enveloped_segment = self._apply_hybrid_envelope(segment, fade_samples)
                    
                    start_s = int(item['start_time'] * SAMPLE_RATE)
                    end_s = start_s + len(enveloped_segment)

                    if end_s > total_samples: continue
                    
                    track[start_s:end_s] += enveloped_segment

            for item in full_drum_data:
                segment = self._generate_percussion_sound(item['drum_type'], item['duration'], SAMPLE_RATE)
                
                start_s = int(item['start_time'] * SAMPLE_RATE)
                end_s = start_s + len(segment)

                if end_s > total_samples: continue
                drum_track[start_s:end_s] += segment

            harmonic_track = np.zeros(total_samples, dtype=np.float64)
            harmonic_track += melody1_track * 0.3
            harmonic_track += melody2_track * 0.3
            harmonic_track += bass_track * 0.2
            harmonic_track += chord_track * 0.2
            
            for track in [harmonic_track, drum_track]:
                if np.max(np.abs(track)) > 0: track /= np.max(np.abs(track))
            
            master_audio = harmonic_track * initial_melody_volume + drum_track * initial_drum_volume
            if ending_style == 'fade_out': master_audio = self._apply_fade_out(master_audio, 4.0, SAMPLE_RATE)
            
            if np.max(np.abs(master_audio)) > 0: master_audio /= np.max(np.abs(master_audio))
            self.last_master_audio = master_audio

            amplitude = 32767.0 if self.last_bit_depth == 16 else 127.0
            def to_stereo_sound(track):
                final_audio = (track * amplitude).astype(np.int16 if self.last_bit_depth == 16 else np.int8)
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
                    log_timeline.append({'start_time': item['start_time'], 'log_type': log_type, 'message': f"Time: {item['start_time']:.2f}s | {notes_str}"})
            
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
        try:
            pygame.mixer.init(frequency=44100, size=-16, channels=16, buffer=1024)
            while True:
                full_song_data, full_drum_data, section_log_timeline, ending_style, total_duration = self._generate_full_song()
                
                print("\n--- SONG GENERATION FINISHED, RENDERING AUDIO... ---\n")

                waveform_type = self.settings.get("waveform", "Sine")
                SAMPLE_RATE = self.last_sample_rate
                
                total_samples = int(total_duration * SAMPLE_RATE) + 10
                melody1_track, melody2_track, bass_track, chord_track, drum_track = (np.zeros(total_samples, dtype=np.float64) for _ in range(5))

                FADE_DURATION_S = 0.005
                fade_samples = int(FADE_DURATION_S * SAMPLE_RATE)

                track_map = {'melody1': melody1_track, 'melody2': melody2_track, 'bass': bass_track, 'chords': chord_track}
                for part_name, track in track_map.items():
                    for item in full_song_data[part_name]:
                        segment = self._generate_tone(item['duration'], SAMPLE_RATE, item['freqs'], waveform_type)
                        enveloped_segment = self._apply_hybrid_envelope(segment, fade_samples)
                        start_s = int(item['start_time'] * SAMPLE_RATE)
                        end_s = start_s + len(enveloped_segment)
                        if end_s <= total_samples:
                            track[start_s:end_s] += enveloped_segment

                for item in full_drum_data:
                    segment = self._generate_percussion_sound(item['drum_type'], item['duration'], SAMPLE_RATE)
                    start_s = int(item['start_time'] * SAMPLE_RATE)
                    end_s = start_s + len(segment)
                    if end_s <= total_samples:
                        drum_track[start_s:end_s] += segment

                harmonic_track = (melody1_track * 0.3) + (melody2_track * 0.3) + (bass_track * 0.2) + (chord_track * 0.2)
                
                for track in [harmonic_track, drum_track]:
                    if np.max(np.abs(track)) > 0: track /= np.max(np.abs(track))
                
                amplitude = 32767.0 if self.last_bit_depth == 16 else 127.0
                def to_stereo_sound(track):
                    final_audio = (track * amplitude).astype(np.int16 if self.last_bit_depth == 16 else np.int8)
                    return pygame.sndarray.make_sound(np.column_stack((final_audio, final_audio)))

                harmonic_sound = to_stereo_sound(harmonic_track)
                drum_sound = to_stereo_sound(drum_track)

                harmonic_channel, drum_channel = pygame.mixer.Channel(0), pygame.mixer.Channel(1)
                
                log_timeline = []
                log_map = {'melody1': 'melody1', 'melody2': 'melody2', 'bass': 'bass', 'chords': 'chords'}
                for part, events in full_song_data.items():
                    log_type = log_map.get(part)
                    if not events or not log_type: continue
                    for item in events:
                        notes_str = ', '.join(self._find_closest_note_name(f) for f in item['freqs'])
                        log_timeline.append({'start_time': item['start_time'], 'log_type': log_type, 'message': f"Time: {item['start_time']:.2f}s | {notes_str}"})
                
                for item in full_drum_data: log_timeline.append({'start_time': item['start_time'], 'log_type': 'drums', 'message': f"Time: {item['start_time']:.2f}s | Drum: {item['drum_type']}"})

                log_timeline.extend(section_log_timeline)
                log_timeline.sort(key=lambda x: x['start_time'])

                print("--- STARTING PLAYBACK ---")
                harmonic_channel.play(harmonic_sound)
                drum_channel.play(drum_sound)

                start_playback_time, log_index = time.time(), 0
                while harmonic_channel.get_busy() or drum_channel.get_busy():
                    elapsed_time = time.time() - start_playback_time
                    while log_index < len(log_timeline) and elapsed_time >= log_timeline[log_index]['start_time']:
                        entry = log_timeline[log_index]; self.update_log(entry['message'], entry['log_type']); log_index += 1
                    time.sleep(0.01)

                print("--- PLAYBACK FINISHED ---")
                
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
            f.setnchannels(2); f.setsampwidth(self.last_bit_depth // 8); f.setframerate(self.last_sample_rate)
            amplitude = 32767.0 if self.last_bit_depth == 16 else 127.0
            audio_data = (self.last_master_audio * amplitude).astype(np.int16 if self.last_bit_depth == 16 else np.int8)
            f.writeframes(np.column_stack((audio_data, audio_data)).tobytes())
        self.update_log(f"Exported to {filename}", 'main')
    
    def export_midi_file(self):
        if not self.last_song_data: self.update_log("No song data to export.", 'main'); return
        filename = filedialog.asksaveasfilename(defaultextension=".mid", filetypes=[("MIDI files", "*.mid")])
        if not filename: return
        
        def freq_to_midi(f): return 69 + 12 * math.log2(f / 440.0)
        
        midi = MIDIFile(5)
        beat_dur = 60.0 / self.last_melody_bpm
        for t in range(5): midi.addTempo(t, 0, self.last_melody_bpm)

        track_map = {'melody1': (0, 0, 100), 'melody2': (1, 1, 90), 'bass': (2, 2, 80), 'chords': (3, 3, 70)}
        for part, (track_num, channel, volume) in track_map.items():
            for item in self.last_song_data[part]:
                start_beat, dur_beats = item['start_time']/beat_dur, item['duration']/beat_dur
                for freq in item['freqs']: midi.addNote(track_num, channel, int(round(freq_to_midi(freq))), start_beat, dur_beats, volume)

        for item in self.last_drum_data: 
            start_beat, dur_beats = item['start_time']/beat_dur, item['duration']/beat_dur
            midi.addNote(4, 9, self.DRUM_SOUND_PROPERTIES[item['drum_type']]['midi_note'], start_beat, dur_beats, 110)
        
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
