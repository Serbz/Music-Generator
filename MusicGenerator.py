# --- Automatic Library Installation ---
import subprocess
import sys

def install_package(package_name, import_name=None):
    """Tries to import a package, installing it if it fails."""
    if import_name is None:
        import_name = package_name
    try:
        __import__(import_name)
        print(f"'{import_name}' is already installed.")
    except ImportError:
        print(f"Library '{import_name}' not found. Attempting to install '{package_name}'...")
        try:
            subprocess.check_call([sys.executable, "-m", "pip", "install", package_name])
        except subprocess.CalledProcessError as e:
            print(f"ERROR: Failed to install '{package_name}'. Please install it manually.")
            print(f"Error details: {e}")
            sys.exit(1)

# Install required packages
install_package('pygame')
install_package('scipy')
install_package('midiutil')
install_package('numpy') # Although a dependency, explicit check is good practice

# --- Main Imports ---
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
from midiutil import MIDIFile
import math
import traceback
import copy
import json

class SpeciesCounterpointEngine:
    """
    A class to handle the rules of species counterpoint for generating a second melody.
    """
    def __init__(self, primary_melody, scale_notes, base_scale_len):
        self.primary_melody = sorted(primary_melody, key=lambda x: x['start_time'])
        self.scale_notes = scale_notes
        self.base_scale_len = base_scale_len
        self.consonant_intervals = {0, 3, 4, 7, 8, 9}  # Unison, thirds, fourths, fifths, sixths (in semitones)

    def _get_interval(self, idx1, idx2):
        # This is a simplification; a full implementation would need the scale's interval map.
        major_intervals = [0, 2, 4, 5, 7, 9, 11]
        semitone1 = major_intervals[idx1 % 7]
        semitone2 = major_intervals[idx2 % 7]
        return abs(semitone1 - semitone2) % 12

    def _is_consonant(self, idx1, idx2):
        return self._get_interval(idx1, idx2) in self.consonant_intervals

    def _avoids_parallels(self, last_m1, last_m2, current_m1, current_m2):
        if last_m1 is None or last_m2 is None:
            return True
        interval1 = self._get_interval(last_m1, last_m2)
        interval2 = self._get_interval(current_m1, current_m2)
        if interval1 == interval2 and interval1 in {0, 7}:  # Parallel unisons/octaves and fifths
            return False
        return True

    def generate_first_species(self, start_idx, m2_waveform, m2_vol_mult):
        events = []
        last_m1_idx, last_m2_idx = None, None
        for event in self.primary_melody:
            if not event.get('scale_idx'): continue
            m1_idx = event['scale_idx'][0]
            
            possible_notes = []
            direction = -1 if m1_idx > start_idx else 1
            for i in range(1, self.base_scale_len):
                candidate_idx = start_idx + (i * direction)
                if self._is_consonant(m1_idx, candidate_idx) and self._avoids_parallels(last_m1_idx, last_m2_idx, m1_idx, candidate_idx):
                    possible_notes.append(candidate_idx)
                
            if not possible_notes: # Fallback
                candidate_idx = start_idx + random.choice([-2, -1, 1, 2])
            else:
                candidate_idx = random.choice(possible_notes)

            m2_idx = max(0, min(len(self.scale_notes) - 1, candidate_idx))
            
            new_event = copy.deepcopy(event)
            new_event.update({
                'scale_idx': [m2_idx],
                'freqs': [self.scale_notes[m2_idx]],
                'waveform': m2_waveform,
                'volume': event['volume'] * m2_vol_mult
            })
            events.append(new_event)
            
            last_m1_idx, last_m2_idx = m1_idx, m2_idx
            start_idx = m2_idx

        return events

class HarmonizerApp:
    def __init__(self, master, ui_mode=True):
        self.master = master
        self.ui_mode = ui_mode
        
        if self.ui_mode:
            master.title("Harmonizer (Advanced Logic)")
            master.geometry("850x800")
            pygame.mixer.init(frequency=44100, size=-16, channels=2, buffer=1024) # Changed to stereo
            master.protocol("WM_DELETE_WINDOW", self.on_closing)
            master.configure(bg='#2e2e2e')

        self.SETTINGS_FILE = "harmonizer_settings.json"
        
        self.melody_channel = None
        self.harmony_channel = None
        self.drum_channel = None
        
        self.lock = threading.Lock()
        self.music_thread = None
        self.stop_event = threading.Event()
        
        self.last_song_data, self.last_drum_data, self.last_master_audio, self.last_melody_bpm = None, None, None, None
        self.last_bit_depth, self.last_sample_rate = 24, 44100
        
        self.last_melody_sound, self.last_harmony_sound, self.last_drum_sound = None, None, None
        self.thematic_seed = None
        self.section_modules = [] # Store thematic fragments

        # --- Debug Window ---
        self.debug_window = None
        self.debug_log_area = None
        
        self.RESONANT_WAVEFORMS = {'Piano', 'Guitar', 'Violin', 'Cello'}
        self.MIN_RESONANT_DURATION = 0.25 # in seconds

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

        self.INTERVAL_NAMES = {
            'Major': self.MAJOR_INTERVALS, 'Dorian': self.DORIAN_INTERVALS, 'Phrygian': self.PHRYGIAN_INTERVALS,
            'Lydian': self.LYDIAN_INTERVALS, 'Mixolydian': self.MIXOLYDIAN_INTERVALS, 'Minor': self.MINOR_INTERVALS,
            'Locrian': self.LOCRIAN_INTERVALS, 'Harmonic Minor': self.HARMONIC_MINOR_INTERVALS,
            'Melodic Minor': self.MELODIC_MINOR_INTERVALS, 'Pentatonic Major': self.PENTATONIC_MAJOR_INTERVALS,
            'Pentatonic Minor': self.PENTATONIC_MINOR_INTERVALS, 'Blues': self.BLUES_INTERVALS,
            'Phrygian Dominant': self.PHRYGIAN_DOMINANT_INTERVALS, 'Custom': self.CUSTOM_INTERVALS,
        }
        self.ROMAN_TO_DEGREE = {
            'i': 0, 'I': 0, 'ii': 1, 'II': 1, 'iii': 2, 'III': 2, 'iv': 3, 'IV': 3,
            'v': 4, 'V': 4, 'vi': 5, 'VI': 5, 'vii': 6, 'VII': 6
        }
        self.CHORD_QUALITIES = {
            'maj': [0, 4, 7], 'min': [0, 3, 7], 'dim': [0, 3, 6],
            'aug': [0, 4, 8], 'dom7': [0, 4, 7, 10], 'half-dim7': [0, 3, 6, 10]
        }

        self.MODAL_CHARACTERISTICS = {
            'Dorian': 6, 'Phrygian': 1, 'Lydian': 4, 'Mixolydian': 6, 'Locrian': 1,
        }
        
        self.MINOR_LIKE_SCALES = {'Minor', 'Dorian', 'Phrygian', 'Locrian', 'Harmonic Minor', 'Melodic Minor', 'Pentatonic Minor', 'Blues'}
        self.MAJOR_LIKE_SCALES = {'Major', 'Lydian', 'Mixolydian', 'Pentatonic Major'}

        self.RHYTHMIC_MOTIFS = {
            'straight': [1, 1, 1, 1], 'syncopated': [0.75, 0.75, 0.5, 1, 1], 'offbeat': [0.5, 1, 0.5, 1, 0.5, 0.5],
            'dotted': [1.5, 0.5, 1.5, 0.5], 'gallop': [0.75, 0.25, 1, 0.75, 0.25, 1],
            'triplet': [1/3, 1/3, 1/3, 1/3, 1/3, 1/3, 1/3, 1/3, 1/3, 1/3, 1/3, 1/3]
        }

        self.ARPEGGIO_RHYTHMS = {
            'eighths': [0.5] * 8,
            'swing': [0.66, 0.34] * 4,
            'dotted': [0.75, 0.25] * 4,
            'mixed': [0.5, 0.25, 0.25, 0.5, 0.5]
        }
        
        self.CLASSICAL_SCHEMAS = {
            'Prinner': {'pattern': [0, -1, -2, -3, -4, 2, 0], 'durations': [1, 0.5, 0.5, 0.5, 0.5, 1, 1]},
            'Meyer': {'pattern': [0, -1, 0, 4, 2, 0], 'durations': [1, 1, 1, 1, 1, 1]},
            'Galant': {'pattern': [0, 1, 2, 0], 'durations': [0.5, 0.5, 0.5, 0.5]}
        }
        
        self.MODAL_INTERCHANGE_MAP = {
            'Major': {'ii': 'ii°', 'iii': 'III+', 'IV': 'iv', 'vi': 'bVI'},
            'Minor': {'iv': 'IV', 'v': 'V', 'VII': 'vii°'}
        }
        
        self.L_SYSTEM_RULES = {
            'A': [{'rule': 'AB', 'weight': 0.6}, {'rule': 'A-B', 'weight': 0.4}],
            'B': [{'rule': 'A', 'weight': 1.0}],
            'transformations': {
                '+': lambda note: {'interval': note['interval'] + 2, 'duration': note['duration']},
                '-': lambda note: {'interval': note['interval'] - 2, 'duration': note['duration']},
                'inv': lambda note: {'interval': -note['interval'], 'duration': note['duration']},
                'aug': lambda note: {'interval': note['interval'], 'duration': note['duration'] * 1.5},
                'dim': lambda note: {'interval': note['interval'], 'duration': note['duration'] / 1.5},
            }
        }
        
        self.AFFECT_PITCH_SETS = {
            'atonal': {'source_sets': [[0,1,4], [0,1,6], [0,2,6]]}
        }


        self.SECONDARY_DOMINANTS = {
            'Major': {'V/ii': 1, 'V/iii': 2, 'V/IV': 3, 'V/V': 4, 'V/vi': 5},
            'Minor': {'V/III': 2, 'V/iv': 3, 'V/V': 4, 'V/VI': 5, 'V/VII': 6}
        }
        self.SECONDARY_LEADING_TONES = {
            'Major': {'vii°7/ii': 1, 'vii°7/iii': 2, 'vii°7/IV': 3, 'vii°7/V': 4, 'vii°7/vi': 5},
            'Minor': {'vii°7/III': 2, 'vii°7/iv': 3, 'vii°7/V': 4, 'vii°7/VI': 5, 'vii°7/VII': 6}
        }
        self.NEAPOLITAN_CHORDS = {'Major': 'bII', 'Minor': 'bII'}
        self.AUGMENTED_SIXTH_CHORDS = {
            'Italian': {'intervals': [0, 6, 8], 'bass_degree': 5},
            'French': {'intervals': [0, 2, 6, 8], 'bass_degree': 5},
            'German': {'intervals': [0, 3, 6, 8], 'bass_degree': 5}
        }

        self.POETIC_METERS = {
            'Iambic': [0.5, 1.0], 'Trochaic': [1.0, 0.5], 'Anapestic': [0.5, 0.5, 1.0],
            'Dactylic': [1.0, 0.5, 0.5], 'Spondaic': [1.0, 1.0], 'Pyrrhic': [0.5, 0.5]
        }
        
        # Based on Simonton's findings: smaller intervals are more probable.
        self.TWO_NOTE_TRANSITIONS = {
            -1: 0.20, 1: 0.20, # Steps
            -2: 0.10, 2: 0.10, # Skips
            0: 0.05, # Repetition
            -3: 0.05, 3: 0.05, # Thirds
            -4: 0.04, 4: 0.04,
            -5: 0.03, 5: 0.03,
            -7: 0.02, 7: 0.02, # Fifths/Octaves
            -12: 0.01, 12: 0.01
        }
        
        self.form_types = ["Standard", "Ternary", "Rondo", "Sonata", "AABA", "Theme and Variations"]

        self.MUSICAL_SCALES = {}
        for note, base_freq in self.NOTE_FREQUENCIES.items():
            for scale_name, intervals in self.INTERVAL_NAMES.items():
                 self.MUSICAL_SCALES[f"{note} {scale_name}"] = [base_freq * (2**(interval/12)) for interval in intervals]

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
            'Pentatonic Major': {'I': [0, 1, 2], 'ii': [1, 2, 3], 'vi': [4, 0, 1]},
            'Pentatonic Minor': {'i': [0, 1, 2], 'iv': [2, 3, 4], 'v': [3, 4, 0]},
            'Blues': {'i': [0, 1, 4], 'iv': [1, 3, 5], 'v': [2, 4, 0]} 
        }
        
        self.CHORD_PROGRESSIONS = {
            'Major': {'intro': ['I', 'IV'], 'verse': ['I', 'vi', 'IV', 'V'], 'pre-chorus': ['ii', 'IV', 'V'], 'chorus': ['I', 'V', 'vi', 'IV'], 'bridge': ['vi', 'V', 'IV', 'IV'], 'solo': ['I', 'V', 'vi', 'IV'], 'outro': ['IV', 'V', 'I', 'I'], 'development': ['ii', 'V', 'I', 'vi'], 'pachelbel': ['I', 'V', 'vi', 'iii', 'IV', 'I', 'IV', 'V'], '50s': ['I', 'vi', 'IV', 'V']},
            'Dorian': {'intro': ['i', 'IV'], 'verse': ['i', 'IV', 'i', 'VII'], 'chorus': ['i', 'IV', 'VII', 'IV'], 'bridge': ['IV', 'VII', 'i', 'i'], 'solo': ['i', 'IV', 'i', 'IV'], 'outro': ['IV', 'i', 'i']},
            'Phrygian': {'intro': ['i', 'II'], 'verse': ['i', 'VI', 'i', 'II'], 'chorus': ['i', 'II', 'VI', 'II'], 'bridge': ['VI', 'vii', 'i', 'i'], 'solo': ['i', 'II', 'i', 'II'], 'outro': ['II', 'i', 'i']},
            'Lydian': {'intro': ['I', 'II'], 'verse': ['I', 'V', 'I', 'II'], 'chorus': ['I', 'II', 'V', 'II'], 'bridge': ['vi', 'V', 'II', 'II'], 'solo': ['I', 'II', 'I', 'II'], 'outro': ['II', 'V', 'I', 'I']},
            'Mixolydian': {'intro': ['I', 'VII'], 'verse': ['I', 'VII', 'IV', 'I'], 'chorus': ['I', 'v', 'IV', 'I'], 'bridge': ['IV', 'v', 'I', 'I'], 'solo': ['I', 'VII', 'IV', 'VII'], 'outro': ['VII', 'IV', 'I', 'I']},
            'Minor': {'intro': ['i', 'VI'], 'verse': ['i', 'VI', 'iv', 'v'], 'pre-chorus': ['ii°', 'VI', 'v'], 'chorus': ['i', 'v', 'VI', 'iv'], 'bridge': ['VI', 'VII', 'i', 'i'], 'solo': ['i', 'v', 'VI', 'iv'], 'outro': ['iv', 'v', 'i', 'i'], 'development': ['ii°', 'v', 'i', 'VI'], 'lament_bridge': ['i', 'VII', 'VI', 'V']},
            'Locrian': {'intro': ['i°', 'iv'], 'verse': ['i°', 'VI', 'iv', 'v°'], 'chorus': ['i°', 'iv', 'V', 'i°'], 'bridge': ['VI', 'V', 'iv', 'iv'], 'solo': ['i°', 'iv', 'i°', 'iv'], 'outro': ['iv', 'V', 'i°', 'i°']},
            'Custom': {'intro': ['i', 'IV+'], 'verse': ['i', 'vi', 'ii', 'V'], 'pre-chorus': ['II', 'V'], 'chorus': ['i', 'V', 'vi', 'IV+'], 'bridge': ['vi', 'V', 'IV+', 'IV+'], 'solo': ['i', 'V', 'vi', 'IV+'], 'outro': ['II', 'V', 'i', 'i'], 'development': ['ii', 'V', 'i', 'vi']},
            'Phrygian Dominant': {'intro': ['i', 'VI'], 'verse': ['i', 'II', 'VI', 'V'], 'pre-chorus': ['iv', 'V'], 'chorus': ['i', 'VI', 'V', 'i'], 'bridge': ['II', 'V', 'i', 'i'], 'solo': ['i', 'VI', 'V', 'i'], 'outro': ['II', 'V', 'i', 'i'], 'development': ['iv', 'V', 'i', 'II']},
            'Harmonic Minor': {'intro': ['i', 'iv'], 'verse': ['i', 'V', 'i', 'VI'], 'pre-chorus': ['ii°', 'V'], 'chorus': ['i', 'VI', 'V'], 'bridge': ['VI', 'V', 'III+'], 'solo': ['i', 'VI', 'V'], 'outro': ['iv', 'v', 'i', 'i'], 'development': ['ii°', 'V', 'VI', 'III+']},
            'Melodic Minor': {'intro': ['i', 'IV'], 'verse': ['i', 'V', 'i', 'vi°'], 'pre-chorus': ['IV', 'V'], 'chorus': ['i', 'vi°', 'V'], 'bridge': ['IV', 'V', 'III+'], 'solo': ['i', 'vi°', 'V'], 'outro': ['IV', 'V', 'i', 'i'], 'development': ['ii', 'V', 'IV', 'III+']},
            'Pentatonic Major': {'intro': ['I'], 'verse': ['I', 'vi', 'I'], 'pre-chorus': ['ii'], 'chorus': ['I', 'vi', 'ii'], 'bridge': ['vi', 'ii', 'I'], 'solo': ['I', 'vi', 'ii'], 'outro': ['ii', 'I', 'I']},
            'Pentatonic Minor': {'intro': ['i'], 'verse': ['i', 'v', 'i'], 'pre-chorus': ['IV'], 'chorus': ['i', 'v', 'IV'], 'bridge': ['v', 'IV', 'i'], 'solo': ['i', 'v', 'IV'], 'outro': ['v', 'i', 'i']},
            'Blues': {'intro': ['i'], 'verse': ['i', 'i', 'i', 'i', 'iv', 'iv', 'i', 'i', 'v', 'iv', 'i', 'i'], 'chorus': ['i', 'iv', 'v'], 'bridge': ['iv', 'iv', 'i', 'i'], 'solo': ['i', 'i', 'i', 'i', 'iv', 'iv', 'i', 'i', 'v', 'iv', 'i', 'i'], 'outro': ['v', 'i', 'i']}
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
        
        self.MIDI_INSTRUMENTS = {
            "Acoustic Grand Piano": 0, "Bright Acoustic Piano": 1, "Electric Grand Piano": 2, "Honky-tonk Piano": 3,
            "Electric Piano 1": 4, "Electric Piano 2": 5, "Harpsichord": 6, "Clavinet": 7, "Celesta": 8, "Glockenspiel": 9,
            "Music Box": 10, "Vibraphone": 11, "Marimba": 12, "Xylophone": 13, "Tubular Bells": 14, "Dulcimer": 15,
            "Drawbar Organ": 16, "Percussive Organ": 17, "Rock Organ": 18, "Church Organ": 19, "Reed Organ": 20,
            "Accordion": 21, "Harmonica": 22, "Tango Accordion": 23, "Acoustic Guitar (nylon)": 24,
            "Acoustic Guitar (steel)": 25, "Electric Guitar (jazz)": 26, "Electric Guitar (clean)": 27,
            "Electric Guitar (muted)": 28, "Overdriven Guitar": 29, "Distortion Guitar": 30, "Guitar Harmonics": 31,
            "Acoustic Bass": 32, "Electric Bass (finger)": 33, "Electric Bass (pick)": 34, "Fretless Bass": 35,
            "Slap Bass 1": 36, "Slap Bass 2": 37, "Synth Bass 1": 38, "Synth Bass 2": 39, "Violin": 40, "Viola": 41,
            "Cello": 42, "Contrabass": 43, "Tremolo Strings": 44, "Pizzicato Strings": 45, "Orchestral Harp": 46,
            "Timpani": 47, "String Ensemble 1": 48, "String Ensemble 2": 49, "Synth Strings 1": 50, "Synth Strings 2": 51,
            "Choir Aahs": 52, "Voice Oohs": 53, "Synth Voice": 54, "Orchestra Hit": 55, "Trumpet": 56, "Trombone": 57,
            "Tuba": 58, "Muted Trumpet": 59, "French Horn": 60, "Brass Section": 61, "Synth Brass 1": 62, "Synth Brass 2": 63,
            "Soprano Sax": 64, "Alto Sax": 65, "Tenor Sax": 66, "Baritone Sax": 67, "Oboe": 68, "English Horn": 69,
            "Bassoon": 70, "Clarinet": 71, "Piccolo": 72, "Flute": 73, "Recorder": 74, "Pan Flute": 75, "Blown Bottle": 76,
            "Shakuhachi": 77, "Whistle": 78, "Ocarina": 79, "Lead 1 (square)": 80, "Lead 2 (sawtooth)": 81,
            "Lead 3 (calliope)": 82, "Lead 4 (chiff)": 83, "Lead 5 (charang)": 84, "Lead 6 (voice)": 85,
            "Lead 7 (fifths)": 86, "Lead 8 (bass + lead)": 87, "Pad 1 (new age)": 88, "Pad 2 (warm)": 89,
            "Pad 3 (polysynth)": 90, "Pad 4 (choir)": 91, "Pad 5 (bowed)": 92, "Pad 6 (metallic)": 93,
            "Pad 7 (halo)": 94, "Pad 8 (sweep)": 95, "FX 1 (rain)": 96, "FX 2 (soundtrack)": 97, "FX 3 (crystal)": 98,
            "FX 4 (atmosphere)": 99, "FX 5 (brightness)": 100, "FX 6 (goblins)": 101, "FX 7 (echoes)": 102,
            "FX 8 (sci-fi)": 103, "Sitar": 104, "Banjo": 105, "Shamisen": 106, "Koto": 107, "Kalimba": 108, "Bag pipe": 109,
            "Fiddle": 110, "Shanai": 111, "Tinkle Bell": 112, "Agogo": 113, "Steel Drums": 114, "Woodblock": 115,
            "Taiko Drum": 116, "Melodic Tom": 117, "Synth Drum": 118, "Reverse Cymbal": 119, "Guitar Fret Noise": 120,
            "Breath Noise": 121, "Seashore": 122, "Bird Tweet": 123, "Telephone Ring": 124, "Helicopter": 125,
            "Applause": 126, "Gunshot": 127
        }
        self.MIDI_INSTRUMENT_NAMES = sorted(self.MIDI_INSTRUMENTS.keys(), key=lambda k: self.MIDI_INSTRUMENTS[k])


        if self.ui_mode:
            self.form_vars = {ft: BooleanVar(value=(ft == "Standard")) for ft in self.form_types}
            self._setup_ui()
        else:
            self.settings = {}

        self.scale_types = sorted(list(set([k.split(' ', 1)[1] for k in self.MUSICAL_SCALES.keys()])))
        if self.ui_mode:
            self.scale_vars = {st: BooleanVar(value=True) for st in self.scale_types}
        else:
            self.scale_vars = {} 
        
        self._load_settings()

        if self.ui_mode:
            self.entry_duration.bind("<KeyRelease>", self._save_settings)
            self.bit_depth_var.trace("w", self._save_settings)

    def _setup_ui(self):
        style = ttk.Style(); style.theme_use('clam'); style.configure("TScale", background="#2e2e2e", troughcolor="#444444")
        style.configure('TRadiobutton', background='#2e2e2e', foreground='white', indicatorrelief=tk.FLAT)
        style.map('TRadiobutton',
            background=[('active', '#3e3e3e')],
            indicatorcolor=[('selected', '#4dbce9'), ('!selected', 'gray')])
        frame = tk.Frame(self.master, padx=10, pady=10, bg='#2e2e2e'); frame.pack(fill=tk.BOTH, expand=True)
        
        # Top Controls
        top_frame = tk.Frame(frame, bg='#2e2e2e'); top_frame.pack(pady=5, fill=tk.X)
        self.play_button = tk.Button(top_frame, text="Play", command=self.start_music, bg='#555555', fg='white'); self.play_button.pack(side=tk.LEFT, padx=5)
        self.replay_button = tk.Button(top_frame, text="Replay", command=self.replay_music, bg='#555555', fg='white', state=tk.DISABLED); self.replay_button.pack(side=tk.LEFT, padx=5)
        self.stop_button = tk.Button(top_frame, text="Stop", command=self.stop_music, bg='#555555', fg='white', state=tk.DISABLED); self.stop_button.pack(side=tk.LEFT, padx=5)
        self.loop_var = BooleanVar(); self.loop_check = tk.Checkbutton(top_frame, text="Loop", variable=self.loop_var, bg='#2e2e2e', fg='white', selectcolor='#444444', command=self._save_settings); self.loop_check.pack(side=tk.LEFT, padx=10)
        self.scales_button = tk.Button(top_frame, text="Scales", command=self._open_scales_window, bg='#4d6b88', fg='white'); self.scales_button.pack(side=tk.LEFT, padx=5)
        self.form_button = tk.Button(top_frame, text="Form", command=self._open_form_window, bg='#4d6b88', fg='white'); self.form_button.pack(side=tk.LEFT, padx=5)

        tk.Label(top_frame, text="Duration (s):", bg='#2e2e2e', fg='white').pack(side=tk.LEFT, padx=(20, 5))
        self.entry_duration = tk.Entry(top_frame, bg='#444444', fg='white', width=10); self.entry_duration.pack(side=tk.LEFT, padx=5)
        self.debug_button = tk.Button(top_frame, text="Debug", command=self.open_debug_window, bg='#4d6b88', fg='white'); self.debug_button.pack(side=tk.RIGHT, padx=5)
        
        # Waveform Controls
        waveform_frame = tk.LabelFrame(frame, text="Waveforms", bg='#2e2e2e', fg='white', padx=5, pady=5); waveform_frame.pack(pady=5, fill=tk.X)
        waveforms = ["Sine", "Square", "Sawtooth", "Triangle", "Piano", "Violin", "Cello", "Guitar", "Rich Saw", "Hollow Square", "Random"]
        self.auto_wave_var = BooleanVar(value=True)
        self.auto_wave_check = tk.Checkbutton(waveform_frame, text="Auto-Select", variable=self.auto_wave_var, bg='#2e2e2e', fg='white', selectcolor='#444444', command=self._save_settings)
        self.auto_wave_check.grid(row=0, column=0, padx=5)
        self.melody1_waveform_var = tk.StringVar(self.master)
        tk.Label(waveform_frame, text="Melody 1:", bg='#2e2e2e', fg='white').grid(row=0, column=1, sticky='e')
        self.m1_waveform_menu = tk.OptionMenu(waveform_frame, self.melody1_waveform_var, *waveforms, command=self._save_settings); self.m1_waveform_menu.grid(row=0, column=2, padx=5)
        self.melody2_waveform_var = tk.StringVar(self.master)
        tk.Label(waveform_frame, text="Melody 2:", bg='#2e2e2e', fg='white').grid(row=0, column=3, sticky='e')
        self.m2_waveform_menu = tk.OptionMenu(waveform_frame, self.melody2_waveform_var, *waveforms, command=self._save_settings); self.m2_waveform_menu.grid(row=0, column=4, padx=5)
        self.chord_waveform_var = tk.StringVar(self.master)
        tk.Label(waveform_frame, text="Chords:", bg='#2e2e2e', fg='white').grid(row=0, column=5, sticky='e')
        self.chord_waveform_menu = tk.OptionMenu(waveform_frame, self.chord_waveform_var, *waveforms, command=self._save_settings); self.chord_waveform_menu.grid(row=0, column=6, padx=5)
        self.bass_waveform_var = tk.StringVar(self.master)
        tk.Label(waveform_frame, text="Bass:", bg='#2e2e2e', fg='white').grid(row=0, column=7, sticky='e')
        self.bass_waveform_menu = tk.OptionMenu(waveform_frame, self.bass_waveform_var, *waveforms, command=self._save_settings); self.bass_waveform_menu.grid(row=0, column=8, padx=5)

        # Mixer & Generation Controls
        mixer_frame = tk.LabelFrame(frame, text="Mixer & Generation", bg='#2e2e2e', fg='white', padx=5, pady=5); mixer_frame.pack(pady=5, fill=tk.X)
        mixer_frame.columnconfigure(1, weight=1); mixer_frame.columnconfigure(3, weight=1); mixer_frame.columnconfigure(5, weight=1); mixer_frame.columnconfigure(7, weight=1)
        tk.Label(mixer_frame, text="Melody Vol:", bg='#2e2e2e', fg='white').grid(row=0, column=0, sticky='e'); self.melody_volume_slider = ttk.Scale(mixer_frame, from_=0, to=100, orient=tk.HORIZONTAL, command=self._update_and_save_melody_volume); self.melody_volume_slider.grid(row=0, column=1, sticky='ew', padx=5)
        tk.Label(mixer_frame, text="Harmony Vol:", bg='#2e2e2e', fg='white').grid(row=0, column=2, sticky='e'); self.harmony_volume_slider = ttk.Scale(mixer_frame, from_=0, to=100, orient=tk.HORIZONTAL, command=self._update_and_save_harmony_volume); self.harmony_volume_slider.grid(row=0, column=3, sticky='ew', padx=5)
        tk.Label(mixer_frame, text="Drum Vol:", bg='#2e2e2e', fg='white').grid(row=0, column=4, sticky='e'); self.drum_volume_slider = ttk.Scale(mixer_frame, from_=0, to=100, orient=tk.HORIZONTAL, command=self._update_and_save_drum_volume); self.drum_volume_slider.grid(row=0, column=5, sticky='ew', padx=5)
        
        # --- Panning Sliders ---
        tk.Label(mixer_frame, text="M1 Pan:", bg='#2e2e2e', fg='white').grid(row=1, column=0, sticky='e'); self.m1_pan_slider = ttk.Scale(mixer_frame, from_=-100, to=100, orient=tk.HORIZONTAL, command=self._save_settings); self.m1_pan_slider.grid(row=1, column=1, sticky='ew', padx=5)
        tk.Label(mixer_frame, text="M2 Pan:", bg='#2e2e2e', fg='white').grid(row=1, column=2, sticky='e'); self.m2_pan_slider = ttk.Scale(mixer_frame, from_=-100, to=100, orient=tk.HORIZONTAL, command=self._save_settings); self.m2_pan_slider.grid(row=1, column=3, sticky='ew', padx=5)
        tk.Label(mixer_frame, text="Chord Pan:", bg='#2e2e2e', fg='white').grid(row=1, column=4, sticky='e'); self.chord_pan_slider = ttk.Scale(mixer_frame, from_=-100, to=100, orient=tk.HORIZONTAL, command=self._save_settings); self.chord_pan_slider.grid(row=1, column=5, sticky='ew', padx=5)
        tk.Label(mixer_frame, text="Bass Pan:", bg='#2e2e2e', fg='white').grid(row=1, column=6, sticky='e'); self.bass_pan_slider = ttk.Scale(mixer_frame, from_=-100, to=100, orient=tk.HORIZONTAL, command=self._save_settings); self.bass_pan_slider.grid(row=1, column=7, sticky='ew', padx=5)

        # Main Log
        main_log_frame = tk.Frame(frame, bg='#2e2e2e'); main_log_frame.pack(pady=5, fill=tk.X)
        tk.Label(main_log_frame, text="Main Events Log", bg='#2e2e2e', fg='white').pack()
        self.main_log_area = scrolledtext.ScrolledText(main_log_frame, wrap=tk.WORD, height=6, state='disabled', bg='black', fg='white'); self.main_log_area.pack(fill=tk.X)
        self.main_log_area.tag_config('main', foreground='lightblue')

        # Log and Export Grid
        grid_frame = tk.Frame(frame, bg='#2e2e2e'); grid_frame.pack(pady=5, fill=tk.BOTH, expand=True)
        grid_frame.grid_columnconfigure(0, weight=1); grid_frame.grid_columnconfigure(1, weight=1)
        grid_frame.grid_rowconfigure(0, weight=1); grid_frame.grid_rowconfigure(1, weight=1)
        grid_frame.grid_rowconfigure(2, weight=1)
        
        melody1_log_frame = tk.LabelFrame(grid_frame, text="Melody 1 Log", bg='#2e2e2e', fg='white'); melody1_log_frame.grid(row=0, column=0, sticky='nsew', padx=2, pady=2)
        self.melody1_log_area = scrolledtext.ScrolledText(melody1_log_frame, wrap=tk.WORD, height=5, state='disabled', bg='black', fg='lightgreen'); self.melody1_log_area.pack(fill=tk.BOTH, expand=True)
        self.melody1_log_area.tag_config('melody1', foreground='lightgreen')
        
        bass_log_frame = tk.LabelFrame(grid_frame, text="Bass Log", bg='#2e2e2e', fg='white'); bass_log_frame.grid(row=0, column=1, sticky='nsew', padx=2, pady=2)
        self.bass_log_area = scrolledtext.ScrolledText(bass_log_frame, wrap=tk.WORD, height=5, state='disabled', bg='black', fg='#FFC0CB'); self.bass_log_area.pack(fill=tk.BOTH, expand=True)
        self.bass_log_area.tag_config('bass', foreground='#FFC0CB')
        
        melody2_log_frame = tk.LabelFrame(grid_frame, text="Melody 2 Log", bg='#2e2e2e', fg='white'); melody2_log_frame.grid(row=1, column=0, sticky='nsew', padx=2, pady=2)
        self.melody2_log_area = scrolledtext.ScrolledText(melody2_log_frame, wrap=tk.WORD, height=5, state='disabled', bg='black', fg='#98FB98'); self.melody2_log_area.pack(fill=tk.BOTH, expand=True)
        self.melody2_log_area.tag_config('melody2', foreground='#98FB98')
        
        chord_log_frame = tk.LabelFrame(grid_frame, text="Chord Log", bg='#2e2e2e', fg='white'); chord_log_frame.grid(row=1, column=1, sticky='nsew', padx=2, pady=2)
        self.chord_log_area = scrolledtext.ScrolledText(chord_log_frame, wrap=tk.WORD, height=5, state='disabled', bg='black', fg='#ADD8E6'); self.chord_log_area.pack(fill=tk.BOTH, expand=True)
        self.chord_log_area.tag_config('chords', foreground='#ADD8E6')
        
        drum_log_frame = tk.LabelFrame(grid_frame, text="Drum Events Log", bg='#2e2e2e', fg='white'); drum_log_frame.grid(row=2, column=0, sticky='nsew', padx=2, pady=2)
        self.drum_log_area = scrolledtext.ScrolledText(drum_log_frame, wrap=tk.WORD, height=5, state='disabled', bg='black', fg='orange'); self.drum_log_area.pack(fill=tk.BOTH, expand=True)
        self.drum_log_area.tag_config('drums', foreground='orange')
        
        # Export and MIDI
        export_reload_frame = tk.LabelFrame(grid_frame, text="Export & MIDI", bg='#2e2e2e', fg='white'); export_reload_frame.grid(row=2, column=1, sticky='nsew', padx=2, pady=2)
        
        # --- NEW: MIDI Instrument Selection Menus ---
        self.midi_m1_var = tk.StringVar(self.master); tk.Label(export_reload_frame, text="M1:", bg='#2e2e2e', fg='white').grid(row=0, column=0); self.midi_m1_menu = tk.OptionMenu(export_reload_frame, self.midi_m1_var, *self.MIDI_INSTRUMENT_NAMES[:20], command=self._save_settings); self.midi_m1_menu.grid(row=0, column=1)
        self.midi_m2_var = tk.StringVar(self.master); tk.Label(export_reload_frame, text="M2:", bg='#2e2e2e', fg='white').grid(row=1, column=0); self.midi_m2_menu = tk.OptionMenu(export_reload_frame, self.midi_m2_var, *self.MIDI_INSTRUMENT_NAMES, command=self._save_settings); self.midi_m2_menu.grid(row=1, column=1)
        self.midi_bass_var = tk.StringVar(self.master); tk.Label(export_reload_frame, text="Bass:", bg='#2e2e2e', fg='white').grid(row=0, column=2); self.midi_bass_menu = tk.OptionMenu(export_reload_frame, self.midi_bass_var, *self.MIDI_INSTRUMENT_NAMES, command=self._save_settings); self.midi_bass_menu.grid(row=0, column=3)
        self.midi_chord_var = tk.StringVar(self.master); tk.Label(export_reload_frame, text="Chords:", bg='#2e2e2e', fg='white').grid(row=1, column=2); self.midi_chord_menu = tk.OptionMenu(export_reload_frame, self.midi_chord_var, *self.MIDI_INSTRUMENT_NAMES, command=self._save_settings); self.midi_chord_menu.grid(row=1, column=3)
        
        export_buttons_frame = tk.Frame(export_reload_frame, bg='#2e2e2e')
        export_buttons_frame.grid(row=2, column=0, columnspan=4, pady=5)
        self.export_wav_button = tk.Button(export_buttons_frame, text="Export WAV", command=self.export_wav_file, bg='#555555', fg='white', state=tk.DISABLED); self.export_wav_button.pack(side=tk.LEFT, padx=5)
        self.bit_depth_var = tk.StringVar(self.master); self.bit_depth_var.set("24")
        tk.Label(export_buttons_frame, text="Bit:", bg='#2e2e2e', fg='white').pack(side=tk.LEFT)
        self.bit_depth_menu = tk.OptionMenu(export_buttons_frame, self.bit_depth_var, "16", "24", command=self._save_settings); self.bit_depth_menu.pack(side=tk.LEFT)
        self.export_midi_button = tk.Button(export_buttons_frame, text="Export MIDI", command=self.export_midi_file, bg='#555555', fg='white', state=tk.DISABLED); self.export_midi_button.pack(side=tk.LEFT, padx=5)
        
        bottom_buttons_frame = tk.Frame(export_reload_frame, bg='#2e2e2e')
        bottom_buttons_frame.grid(row=3, column=0, columnspan=4, sticky='e', pady=5)
        self.help_button = tk.Button(bottom_buttons_frame, text="Help", command=self._open_help_window, bg='#4d6b88', fg='white'); self.help_button.pack(side=tk.LEFT, padx=5)
        self.reload_button = tk.Button(bottom_buttons_frame, text="Reload", command=self.reload_script, bg='#884d4d', fg='white'); self.reload_button.pack(side=tk.LEFT, padx=5)

    def _save_settings(self, *args):
        settings = {
            "duration": self.entry_duration.get(), "bit_depth": self.bit_depth_var.get(), "auto_wave": self.auto_wave_var.get(),
            "m1_waveform": self.melody1_waveform_var.get(), "m2_waveform": self.melody2_waveform_var.get(),
            "chord_waveform": self.chord_waveform_var.get(), "bass_waveform": self.bass_waveform_var.get(),
            "loop": self.loop_var.get(), 
            "forms": {ft: var.get() for ft, var in self.form_vars.items()},
            "melody_vol": self.melody_volume_slider.get(), "harmony_vol": self.harmony_volume_slider.get(), "drum_vol": self.drum_volume_slider.get(),
            "scales": {st: var.get() for st, var in self.scale_vars.items()},
            "m1_pan": self.m1_pan_slider.get(), "m2_pan": self.m2_pan_slider.get(),
            "chord_pan": self.chord_pan_slider.get(), "bass_pan": self.bass_pan_slider.get(),
            "midi_m1": self.midi_m1_var.get(), "midi_m2": self.midi_m2_var.get(),
            "midi_chord": self.midi_chord_var.get(), "midi_bass": self.midi_bass_var.get(),
        }
        try:
            with open(self.SETTINGS_FILE, 'w') as f: json.dump(settings, f, indent=4)
        except Exception as e: self.update_log(f"Error saving settings: {e}", 'main')

    def _load_settings(self):
        try:
            if os.path.exists(self.SETTINGS_FILE):
                with open(self.SETTINGS_FILE, 'r') as f: settings = json.load(f)
            else: settings = {}

            if self.ui_mode:
                self.entry_duration.delete(0, tk.END); self.entry_duration.insert(0, settings.get("duration", "60"))
                self.bit_depth_var.set(settings.get("bit_depth", "24")); self.auto_wave_var.set(settings.get("auto_wave", True))
                self.melody1_waveform_var.set(settings.get("m1_waveform", "Piano")); self.melody2_waveform_var.set(settings.get("m2_waveform", "Sine"))
                self.chord_waveform_var.set(settings.get("m2_waveform", "Violin"))
                self.chord_waveform_var.set(settings.get("chord_waveform", "Synth Pad")); self.bass_waveform_var.set(settings.get("bass_waveform", "Square"))
                self.loop_var.set(settings.get("loop", False))
                
                loaded_forms = settings.get("forms", {})
                for ft, var in self.form_vars.items():
                    var.set(loaded_forms.get(ft, (ft == "Standard")))

                self.melody_volume_slider.set(settings.get("melody_vol", 70.0)); self.harmony_volume_slider.set(settings.get("harmony_vol", 70.0)); self.drum_volume_slider.set(settings.get("drum_vol", 70.0))
                
                self.m1_pan_slider.set(settings.get("m1_pan", -20.0))
                self.m2_pan_slider.set(settings.get("m2_pan", 20.0))
                self.chord_pan_slider.set(settings.get("chord_pan", 0.0))
                self.bass_pan_slider.set(settings.get("bass_pan", 0.0))
                self.midi_m1_var.set(settings.get("midi_m1", "Acoustic Grand Piano"))
                self.midi_m2_var.set(settings.get("midi_m2", "Synth Strings 1"))
                self.midi_chord_var.set(settings.get("midi_chord", "String Ensemble 1"))
                self.midi_bass_var.set(settings.get("midi_bass", "Acoustic Bass"))

            else:
                self.settings = { "duration": settings.get("duration", "90"), "bit_depth": settings.get("bit_depth", "24"), "m1_waveform": settings.get("m1_waveform", "Piano"), "m2_waveform": settings.get("m2_waveform", "Sine"), "chord_waveform": settings.get("chord_waveform", "Synth Pad"), "bass_waveform": settings.get("bass_waveform", "Square"), "form": settings.get("form", "Standard") }
            
            loaded_scales = settings.get("scales", {})
            if self.ui_mode:
                for st, var in self.scale_vars.items(): var.set(loaded_scales.get(st, True))
            else:
                self.scale_vars = {st: loaded_scales.get(st, True) for st in self.scale_types}
                self.settings["scales"] = self.scale_vars
            if self.debug_log_area:
                self.update_log(f"Loaded settings: {settings}", 'debug', debug_only=True)
        except Exception as e: 
            self.update_log(f"Error loading settings: {e}", 'main')
            self.update_log(traceback.format_exc(), 'debug', debug_only=True)

    def _open_help_window(self):
        help_win = tk.Toplevel(self.master)
        help_win.title("Harmonizer Help")
        help_win.geometry("700x600")
        help_win.configure(bg='#2e2e2e')

        st = scrolledtext.ScrolledText(help_win, wrap=tk.WORD, bg='#333333', fg='white', padx=10, pady=10)
        st.pack(fill=tk.BOTH, expand=True)

        st.tag_configure('title', font=('Helvetica', 16, 'bold'), foreground='#4dbce9', spacing3=10)
        st.tag_configure('heading', font=('Helvetica', 12, 'bold'), foreground='#a6e22e', spacing1=10, spacing3=5)
        st.tag_configure('param', font=('Helvetica', 10, 'bold'), foreground='#f92672')

        help_text = [
            ("Harmonizer Help Guide\n\n", 'title'),
            ("This guide explains the function of each control in the Harmonizer application.\n\n", ''),
            ("Main Controls\n", 'heading'),
            ("Play:", 'param'), (" Generates and plays a new song based on the current settings.\n", ''),
            ("Replay:", 'param'), (" Plays the last generated song again without regenerating.\n", ''),
            ("Stop:", 'param'), (" Stops the current playback or generation process.\n", ''),
            ("Loop:", 'param'), (" If checked, a new song will automatically generate and play after the current one finishes.\n\n", ''),
            ("Musical Parameters\n", 'heading'),
            ("Form:", 'param'), (" Opens a window to enable or disable song structures. The generator will randomly pick from the enabled options.\n", ''),
            ("Duration (s):", 'param'), (" The total length of the generated piece in seconds.\n", ''),
            ("Scales:", 'param'), (" Opens a window to enable or disable specific musical scales that the generator can choose from.\n\n", ''),
            ("Waveforms\n", 'heading'),
            ("Auto-Select:", 'param'), (" When checked, the application intelligently picks instrument sounds (waveforms) based on the song's generated 'affect' (e.g., uplifting, melancholy).\n", ''),
            ("Melody 1/2, Chords, Bass:", 'param'), (" Manually select the waveform for each musical part. 'Random' will pick a new sound for that part each time you play.\n\n", ''),
            ("Mixer & Generation\n", 'heading'),
            ("Volume Sliders:", 'param'), (" Control the loudness of the Melody (1 & 2 combined), Harmony (Chords & Bass combined), and Drums.\n", ''),
            ("Pan Sliders (M1, M2, Chord, Bass):", 'param'), (" Position each instrument in the stereo field. -100 is hard left, 0 is center, and 100 is hard right.\n\n", ''),
            ("Export & MIDI\n", 'heading'),
            ("MIDI Instrument Menus:", 'param'), (" Select the General MIDI instrument sound that will be assigned to each part when you export a MIDI file. This does not affect the audio playback in the app.\n", ''),
            ("Export WAV:", 'param'), (" Saves the last generated song as a high-quality stereo WAV audio file.\n", ''),
            ("Export MIDI:", 'param'), (" Saves the last generated song as a MIDI file, which can be used in other music software.\n", ''),
            ("Reload:", 'param'), (" Restarts the script. Useful if the application becomes unresponsive.\n", ''),
        ]

        for text, tag in help_text:
            st.insert(tk.END, text, tag)
        
        st.configure(state='disabled')


    def _open_scales_window(self):
        scales_win = tk.Toplevel(self.master); scales_win.title("Enabled Scales"); scales_win.configure(bg='#2e2e2e')
        main_frame = tk.Frame(scales_win, padx=10, pady=10, bg='#2e2e2e'); main_frame.pack()
        num_scales = len(self.scale_types); num_cols = 2
        for i, scale_type in enumerate(self.scale_types):
            var = self.scale_vars[scale_type]
            row = i % ( (num_scales + 1) // num_cols ); col = i // ( (num_scales + 1) // num_cols )
            cb = tk.Checkbutton(main_frame, text=scale_type, variable=var, bg='#2e2e2e', fg='white', selectcolor='#444444', command=self._save_settings)
            cb.grid(row=row, column=col, sticky='w', padx=5, pady=2)

    def _open_form_window(self):
        form_win = tk.Toplevel(self.master)
        form_win.title("Enabled Forms")
        form_win.configure(bg='#2e2e2e')
        main_frame = tk.Frame(form_win, padx=10, pady=10, bg='#2e2e2e')
        main_frame.pack()

        tk.Label(main_frame, text="Select desired song structures:", bg='#2e2e2e', fg='white').pack(anchor='w', pady=(0, 5))

        for form_type in self.form_types:
            var = self.form_vars[form_type]
            cb = tk.Checkbutton(main_frame, text=form_type, variable=var, bg='#2e2e2e', fg='white', selectcolor='#444444', command=self._save_settings)
            cb.pack(anchor='w', padx=5, pady=2)

    def open_debug_window(self):
        if self.debug_window is None or not self.debug_window.winfo_exists():
            self.debug_window = tk.Toplevel(self.master); self.debug_window.title("Debug Log"); self.debug_window.geometry("800x600")
            self.debug_log_area = scrolledtext.ScrolledText(self.debug_window, wrap=tk.WORD, state='disabled', bg='black', fg='white')
            self.debug_log_area.pack(fill=tk.BOTH, expand=True)
            self.debug_window.protocol("WM_DELETE_WINDOW", self.on_debug_close)
            self.update_log("Debug window opened.", 'debug', debug_only=True)

    def on_debug_close(self):
        self.debug_window.destroy(); self.debug_window = None; self.debug_log_area = None

    def _get_related_key(self, base_key_name, relation='dominant'):
        self.update_log(f"Getting related key for {base_key_name} with relation {relation}", 'debug', debug_only=True)
        base_note, scale_kind = base_key_name.split(' ', 1); base_note_index = self.ALL_NOTES.index(base_note)
        relations = {'dominant': 7, 'subdominant': 5, 'relative_major': 3, 'relative_minor': -3, 'chromatic_mediant_up': 4, 'chromatic_mediant_down': -4, 'tritone': 6}
        if relation in relations:
            related_index = (base_note_index + relations[relation]) % 12
            new_kind = 'Major' if 'Minor' in scale_kind else 'Minor' if 'relative' in relation else scale_kind
            related_key = f"{self.ALL_NOTES[related_index]} {new_kind}"
            self.update_log(f"  -> Found related key: {related_key}", 'debug', debug_only=True)
            return related_key
        return f"{self.ALL_NOTES[(base_note_index + 7) % 12]} {scale_kind}"

    def _get_contrapuntal_motion(self, m1_direction):
        if m1_direction == 0: return 'oblique'
        return random.choices(['similar', 'contrary', 'oblique'], [0.4, 0.5, 0.1])[0]

    def _find_closest_note_name(self, freq):
        min_dist, closest_name = float('inf'), "N/A"
        for note_name, base_freq in self.NOTE_FREQUENCIES.items():
            for octave in range(2, 7):
                note_freq_in_octave = base_freq * (2**(octave-4))
                if abs(freq - note_freq_in_octave) < min_dist:
                    min_dist, closest_name = abs(freq - note_freq_in_octave), f"{note_name}{octave}"
        return closest_name
    
    def _generate_urlinie(self, num_events, base_scale_len):
        """
        Generates a Schenkerian Urlinie (background line), typically a simple descent.
        """
        start_degree = random.choice([2, 4])  # 0-indexed for 3rd, 5th
        end_degree = 0 # Tonic
        urlinie_degrees = np.linspace(start_degree, end_degree, num_events).astype(int)
        urlinie_indices = [d + (base_scale_len * 2) for d in urlinie_degrees]
        self.update_log(f"Generated Schenkerian Urlinie (background structure): {urlinie_indices}", 'debug', debug_only=True)
        return urlinie_indices

    def _generate_l_system_melody(self, axiom, generations):
        """
        Generates a sequence of melodic transformations using an L-System.
        """
        current_string = "A" 
        for _ in range(generations):
            next_string = ""
            for char in current_string:
                if char in self.L_SYSTEM_RULES:
                    rules = self.L_SYSTEM_RULES[char]
                    weights = [r['weight'] for r in rules]
                    chosen_rule = random.choices(rules, weights=weights, k=1)[0]['rule']
                    next_string += chosen_rule
                else:
                    next_string += char
            current_string = next_string

        self.update_log(f"L-System generated string: {current_string}", 'debug', debug_only=True)
        
        final_melody_sequence = []
        for char in current_string:
            transformed_axiom = copy.deepcopy(axiom)
            if char in self.L_SYSTEM_RULES['transformations']:
                 transformed_axiom = [self.L_SYSTEM_RULES['transformations'][char](note) for note in transformed_axiom]
            final_melody_sequence.append(transformed_axiom)
            
        return final_melody_sequence

    def _humanize_part(self, events, dynamics_level):
        """Adds subtle, random variations to timing and volume to simulate a human performance."""
        if not events: return events
        humanized_events = []
        # Max timing variation in seconds (related to beat duration)
        time_variance = (60.0 / self.last_melody_bpm) * 0.05 
        # Max volume variation (related to dynamics setting)
        volume_variance = 0.1 + (dynamics_level * 0.2)

        for event in events:
            new_event = copy.deepcopy(event)
            # Random timing offset
            time_offset = random.uniform(-time_variance, time_variance)
            new_event['start_time'] = max(0, new_event['start_time'] + time_offset)
            
            # Random volume offset
            volume_offset = random.uniform(-volume_variance, volume_variance)
            new_event['volume'] = max(0.1, min(1.0, new_event['volume'] + volume_offset))
            
            humanized_events.append(new_event)
        return humanized_events

    def _apply_dynamic_contouring(self, events, dynamics_level):
        """Applies crescendos/decrescendos based on melodic contour."""
        if len(events) < 3: return events
        
        contoured_events = copy.deepcopy(events)
        for i in range(1, len(contoured_events) - 1):
            prev_note_idx = contoured_events[i-1]['scale_idx'][0] if contoured_events[i-1].get('scale_idx') else 0
            curr_note_idx = contoured_events[i]['scale_idx'][0] if contoured_events[i].get('scale_idx') else 0
            next_note_idx = contoured_events[i+1]['scale_idx'][0] if contoured_events[i+1].get('scale_idx') else 0

            # Simple contour detection: rising, falling, peak, valley
            if curr_note_idx > prev_note_idx and curr_note_idx < next_note_idx: # Rising line
                contoured_events[i]['volume'] *= (1.0 + 0.1 * dynamics_level)
            elif curr_note_idx > prev_note_idx and curr_note_idx > next_note_idx: # Peak
                contoured_events[i]['volume'] *= (1.0 + 0.2 * dynamics_level)
            elif curr_note_idx < prev_note_idx and curr_note_idx > next_note_idx: # Valley
                 contoured_events[i]['volume'] *= (1.0 - 0.2 * dynamics_level)
            elif curr_note_idx < prev_note_idx and curr_note_idx < next_note_idx: # Approaching valley
                 contoured_events[i]['volume'] *= (1.0 - 0.1 * dynamics_level)

            contoured_events[i]['volume'] = max(0.1, min(1.0, contoured_events[i]['volume']))
        return contoured_events

    def _generate_melodic_note(self, current_note_index, last_note_index, scale_notes, current_chord_indices, last_direction, consecutive_steps, scale_type, log_callback, contour, phrase_progress, tension=0.5, target_note_idx=None, characteristic_note_idx=None, pitch_class_set=None):
        log_callback(f"    Melody Note Gen Start: current_idx={current_note_index}, last_idx={last_note_index}, contour={contour}, target_note={target_note_idx}, tension={tension:.2f}", 'debug', debug_only=True)
        scale_length = len(scale_notes)
        base_scale_len = 12 if pitch_class_set is not None else (len(self.INTERVAL_NAMES.get(scale_type, [])))
        next_note_index, next_direction, consecutive_steps_new, rule_applied = current_note_index, last_direction, consecutive_steps, "No rule"

        # Atonal logic using Pitch-Class Sets
        if pitch_class_set is not None:
            # ... (existing atonal logic) ...
            return max(0, min(scale_length - 1, next_note_index)), np.sign(next_note_index - current_note_index), 0

        # Probabilistic melodic generation
        weights = self.TWO_NOTE_TRANSITIONS.copy()
        
        # Apply tension: Higher tension favors larger/rarer intervals
        for interval, prob in weights.items():
            if abs(interval) > 2:
                weights[interval] = prob * (1 + tension)
            elif abs(interval) <= 1:
                 weights[interval] = prob * (1 - tension * 0.5)

        # Strong pull towards target notes (Schenkerian/structural)
        if target_note_idx is not None:
            direction_to_target = np.sign(target_note_idx - current_note_index)
            if direction_to_target != 0:
                if direction_to_target in weights:
                    weights[direction_to_target] *= 5 # Strong bias
                else: # Handle larger jumps to target
                    weights[direction_to_target] = 0.1 

        # Contour bias
        contour_bias = 0
        if contour == 'rising': contour_bias = 1
        elif contour == 'falling': contour_bias = -1
        elif contour == 'arch': contour_bias = 1 if phrase_progress < 0.5 else -1
        elif contour == 'valley': contour_bias = -1 if phrase_progress < 0.5 else 1
        
        if contour_bias in weights:
            weights[contour_bias] *= 1.5

        # Avoid excessive repetition or zig-zag
        if last_direction in weights:
            weights[last_direction] *= 1.2 # Inertia
        if -last_direction in weights and consecutive_steps > 3:
            weights[-last_direction] *= 1.8 # Break long runs

        # Choose next interval based on weighted probabilities
        possible_intervals = list(weights.keys())
        probabilities = np.array(list(weights.values()))
        probabilities /= probabilities.sum() # Normalize
        
        chosen_interval = np.random.choice(possible_intervals, p=probabilities)
        next_note_index = current_note_index + chosen_interval
        
        consecutive_steps_new = consecutive_steps + 1 if np.sign(chosen_interval) == last_direction else 1
        next_direction = np.sign(chosen_interval)
        
        log_callback(f"    Probabilistic Choice: Interval={chosen_interval} -> New Index: {next_note_index}", 'debug', debug_only=True)
        next_note_index = max(0, min(scale_length - 1, next_note_index))
        return next_note_index, next_direction, consecutive_steps_new

    def _generate_rich_saw(self, freq, duration, sample_rate, num_harmonics=8, detune_factor=0.01):
        t = np.linspace(0, duration, int(duration * sample_rate), False); wave = np.zeros_like(t)
        lfo = 0.005 * np.sin(2 * np.pi * random.uniform(4, 7) * t)
        for i in range(1, num_harmonics + 1):
            detune = 1 + (random.random() - 0.5) * detune_factor; amplitude = 1.0 / (i**0.8)
            wave += amplitude * signal.sawtooth(2 * np.pi * freq * i * detune * (1 + lfo) * t)
        return wave
        
    def _generate_hollow_square(self, freq, duration, sample_rate):
        num_samples = int(duration * sample_rate); t = np.linspace(0, duration, num_samples, False)
        wave1, wave2 = signal.square(2 * np.pi * freq * t), signal.square(2 * np.pi * freq * t + np.pi / 2.5)
        b, a = signal.butter(2, 2500 / (0.5 * sample_rate), btype='low'); filtered_wave = signal.lfilter(b, a, wave1 + wave2)
        attack_samples, release_samples = min(int(0.02*sample_rate), num_samples//2), min(int(0.1*sample_rate), num_samples//2)
        sustain_samples = num_samples - attack_samples - release_samples
        env = np.concatenate([np.linspace(0, 1, attack_samples) if attack_samples > 0 else [], np.ones(sustain_samples) if sustain_samples > 0 else [], np.linspace(1, 0, release_samples) if release_samples > 0 else []])
        return filtered_wave * env
        
    def _generate_violin(self, freq, duration, sample_rate):
        num_samples = int(duration * sample_rate)
        t = np.linspace(0, duration, num_samples, False)
        
        vibrato_rate = random.uniform(5.5, 6.5)
        vibrato_depth = 0.012
        phase_increment = (2 * np.pi * (freq/2) / sample_rate) * (1 + vibrato_depth * np.sin(2 * np.pi * vibrato_rate * t))
        phase = np.cumsum(phase_increment)

        saw_wave = signal.sawtooth(phase)
        triangle_wave = signal.sawtooth(phase * 1.002, width=0.5) # Slight detune
        bow_noise = np.random.normal(0, 0.03, num_samples)
        wave = (saw_wave * 0.65) + (triangle_wave * 0.35) + bow_noise

        formant_intensity = 1.0 + 0.1 * np.sin(2 * np.pi * 1.5 * t)
        
        formants = [ (550, 15), (2500, 10), (4000, 9) ]
        body_filtered_wave = np.zeros_like(wave)
        for res_freq, Q in formants:
            b_res, a_res = signal.iirpeak(res_freq, Q, fs=sample_rate)
            body_filtered_wave += signal.lfilter(b_res, a_res, wave * formant_intensity)
        
        if formants: body_filtered_wave /= len(formants)

        b_lp, a_lp = signal.butter(2, 6000 / (0.5 * sample_rate), btype='low')
        final_wave = signal.lfilter(b_lp, a_lp, body_filtered_wave)

        attack_time = 0.08; release_time = 0.15
        attack_samples = min(int(attack_time * sample_rate), num_samples//2)
        release_samples = min(int(release_time * sample_rate), num_samples//2)
        sustain_samples = num_samples - attack_samples - release_samples
        if sustain_samples < 0:
            attack_samples = int(num_samples * (attack_time / (attack_time + release_time)))
            release_samples = num_samples - attack_samples
            sustain_samples = 0

        env = np.concatenate([
            np.linspace(0, 1, attack_samples)**1.5 if attack_samples > 0 else [], 
            np.full(sustain_samples, 1.0) if sustain_samples > 0 else [], 
            np.linspace(1, 0, release_samples)**2.5 if release_samples > 0 else []
        ])
        return final_wave * env

    def _generate_cello(self, freq, duration, sample_rate):
        num_samples = int(duration * sample_rate)
        t = np.linspace(0, duration, num_samples, False)
        base_freq = freq / 2
        vibrato_rate = random.uniform(4.8, 5.5)
        vibrato_depth = 0.009
        phase_increment = (2 * np.pi * base_freq / sample_rate) * (1 + vibrato_depth * np.sin(2 * np.pi * vibrato_rate * t))
        phase = np.cumsum(phase_increment)

        saw_wave = signal.sawtooth(phase)
        triangle_wave = signal.sawtooth(phase * 1.003, width=0.5) 
        sine_wave = np.sin(phase)
        bow_noise = np.random.normal(0, 0.025, num_samples) 
        wave = (saw_wave * 0.5) + (triangle_wave * 0.4) + (sine_wave * 0.1) + bow_noise

        formant_intensity_envelope = 1.0 + 0.05 * np.sin(2 * np.pi * 1.2 * t)
        formants = [ (250, 9), (500, 11), (1500, 8), (3500, 7) ]
        body_filtered_wave = np.zeros_like(wave)
        wave_modulated = wave * formant_intensity_envelope
        
        for res_freq, Q in formants:
            b_res, a_res = signal.iirpeak(res_freq, Q, fs=sample_rate)
            body_filtered_wave += signal.lfilter(b_res, a_res, wave_modulated)
        
        if formants: body_filtered_wave /= len(formants)

        b_lp, a_lp = signal.butter(2, 3800 / (0.5 * sample_rate), btype='low') 
        final_wave = signal.lfilter(b_lp, a_lp, body_filtered_wave)

        attack_time, release_time = 0.1, 0.3
        attack_samples = min(int(attack_time * sample_rate), num_samples // 2)
        release_samples = min(int(release_time * sample_rate), num_samples // 2)
        sustain_samples = num_samples - attack_samples - release_samples

        if sustain_samples < 0:
            attack_samples = int(num_samples * (attack_time / (attack_time + release_time)))
            release_samples = num_samples - attack_samples
            sustain_samples = 0
            
        env = np.concatenate([
            np.linspace(0, 1, attack_samples)**1.3 if attack_samples > 0 else [], 
            np.full(sustain_samples, 1.0) if sustain_samples > 0 else [], 
            np.linspace(1, 0, release_samples)**2.2 if release_samples > 0 else []
        ])
        return final_wave * env

    def _generate_guitar(self, freq, duration, sample_rate):
        num_samples = int(duration * sample_rate)
        t = np.linspace(0, duration, num_samples, False)
        wave = np.zeros(num_samples)
        num_harmonics = 20; inharmonicity_B = 0.0001
        pluck_pos = 1/3.0 
        for k in range(1, num_harmonics + 1):
            pluck_factor = np.sin(k * np.pi * pluck_pos)
            if abs(pluck_factor) < 1e-6: continue
            partial_freq = k * freq/2 * np.sqrt(1 + inharmonicity_B * k**2)
            if partial_freq > sample_rate / 2: continue
            decay_rate = 2.0 + k * 0.8 + (k**2) * 0.05
            envelope = np.exp(-decay_rate * t)
            amplitude = pluck_factor / (k**1.1)
            wave += amplitude * np.sin(2 * np.pi * partial_freq * t) * envelope
        b, a = signal.butter(2, 5000 / (0.5 * sample_rate), btype='low')
        filtered_wave = signal.lfilter(b, a, wave)
        attack_time = 0.005
        attack_samples = int(attack_time * sample_rate)
        if attack_samples > 0 and num_samples > attack_samples:
           filtered_wave[:attack_samples] *= np.linspace(0, 1, attack_samples)
        return filtered_wave

    def _apply_adsr_envelope(self, audio_data, attack_time, decay_time, sustain_level, release_time, sample_rate):
        num_samples = len(audio_data)
        attack_samples = int(attack_time * sample_rate)
        decay_samples = int(decay_time * sample_rate)
        release_samples = int(release_time * sample_rate)
        
        sustain_samples = num_samples - attack_samples - decay_samples - release_samples
        
        if sustain_samples < 0:
            release_samples = max(0, release_samples + sustain_samples)
            sustain_samples = 0
            decay_samples = max(0, decay_samples + sustain_samples)
        
        envelope = np.zeros(num_samples)
        
        if attack_samples > 0:
            envelope[:attack_samples] = np.linspace(0, 1, attack_samples)
        
        if decay_samples > 0:
            envelope[attack_samples:attack_samples+decay_samples] = np.linspace(1, sustain_level, decay_samples)
            
        if sustain_samples > 0:
            envelope[attack_samples+decay_samples:-release_samples] = sustain_level
            
        if release_samples > 0:
            envelope[-release_samples:] = np.linspace(sustain_level, 0, release_samples)

        return audio_data * envelope

    def _generate_tone(self, duration_sec, sample_rate, freqs, waveform_type):
        self.update_log(f"Generating tone: {waveform_type} at {freqs} Hz for {duration_sec}s", 'debug', debug_only=True)
        if not isinstance(freqs, list): freqs = [freqs]
        num_samples = int(duration_sec * sample_rate)
        if num_samples <= 0: return np.zeros(0)
        t = np.linspace(0, duration_sec, num_samples, False)
        
        combined_audio = np.zeros(num_samples)
        if not freqs: return combined_audio

        for frequency in freqs:
            audio_data = np.zeros(num_samples)
            
            is_basic_waveform = False
            if waveform_type == 'Square': 
                audio_data = np.sign(np.sin(frequency * t * 2 * np.pi))
                is_basic_waveform = True
            elif waveform_type == 'Sawtooth': 
                audio_data = signal.sawtooth(2 * np.pi * frequency * t)
                is_basic_waveform = True
            elif waveform_type == 'Triangle': 
                audio_data = signal.sawtooth(2 * np.pi * frequency * t, width=0.5)
                is_basic_waveform = True
            
            elif waveform_type == 'Piano':
                piano_gain = 1.0 
                num_partials = 16
                log_freq = np.log2(max(frequency, 20) / 20)
                # Inharmonicity: Upper partials are sharper than pure harmonics
                inharmonicity_B = 0.0001 + 0.0004 * (1 - np.sin(np.pi * log_freq / 10))
                decay_slow_base = 0.2 + (frequency / 2000.0) * 0.8 
                decay_fast_base = 6.0 + (frequency / 2000.0) * 2.0
                decay_freq_factor = 0.0005
                amp_fast_component = 0.6 + 0.3 * (log_freq / 10)
                # Beating effect from multiple strings
                beating_factor = 1.0005 
                ref_freq_piano = 440.0
                boost_factor = (max(ref_freq_piano, frequency) / ref_freq_piano)**0.25
                piano_gain *= boost_factor
                
                for k in range(1, num_partials + 1):
                    # Apply inharmonicity
                    partial_freq = k * frequency * np.sqrt(1 + inharmonicity_B * k**2)
                    if partial_freq > sample_rate / 2: continue
                    decay_fast = decay_fast_base + partial_freq * decay_freq_factor
                    decay_slow = decay_slow_base + partial_freq * decay_freq_factor * 0.5
                    env_fast = np.exp(-decay_fast * t); wave_fast = np.sin(2 * np.pi * partial_freq * t)
                    # Create two slightly detuned waves for beating/chorus effect
                    env_slow = np.exp(-decay_slow * t); wave_slow = np.sin(2 * np.pi * partial_freq * beating_factor * t)
                    partial_amplitude = np.exp(-0.0008 * partial_freq) / k
                    combined_partial = partial_amplitude * (amp_fast_component * wave_fast * env_fast + (1 - amp_fast_component) * wave_slow * env_slow)
                    audio_data += combined_partial
                
                soundboard_resonances = [(90, 20), (160, 15), (300, 10)]
                soundboard_filtered = np.zeros_like(audio_data)
                for res_freq, Q in soundboard_resonances:
                    b_res, a_res = signal.iirpeak(res_freq, Q, fs=sample_rate)
                    soundboard_filtered += signal.lfilter(b_res, a_res, audio_data)
                
                b_lp, a_lp = signal.butter(2, 6000, 'low', fs=sample_rate)
                audio_data = signal.lfilter(b_lp, a_lp, soundboard_filtered)
                
                attack_time = 0.002 + 0.02 * (1 - (log_freq / 10))
                attack_samples = min(int(attack_time * sample_rate), num_samples)
                if attack_samples > 0:
                    attack_env = np.linspace(0, 1, attack_samples)**1.5
                    audio_data[:attack_samples] *= attack_env

                release_time = 0.08
                release_samples = min(int(release_time * sample_rate), num_samples)
                if release_samples > 0:
                    release_env = np.linspace(1, 0, release_samples)**2
                    audio_data[-release_samples:] *= release_env

                audio_data *= piano_gain

            elif waveform_type == 'Violin': audio_data = self._generate_violin(frequency, duration_sec, sample_rate)
            elif waveform_type == 'Cello': audio_data = self._generate_cello(frequency, duration_sec, sample_rate)
            elif waveform_type == 'Guitar': audio_data = self._generate_guitar(frequency, duration_sec, sample_rate)
            elif waveform_type == 'Rich Saw': audio_data = self._generate_rich_saw(frequency, duration_sec, sample_rate)
            elif waveform_type == 'Hollow Square': audio_data = self._generate_hollow_square(frequency, duration_sec, sample_rate)
            else: 
                audio_data = np.sin(frequency * t * 2 * np.pi)
                is_basic_waveform = True

            if is_basic_waveform:
                attack, decay, sustain, release = 0.02, 0.1, 0.7, 0.2
                if release > duration_sec:
                    release = duration_sec * 0.5; attack = duration_sec * 0.1; decay = duration_sec * 0.1
                audio_data = self._apply_adsr_envelope(audio_data, attack, decay, sustain, release, sample_rate)
            
            combined_audio += audio_data

        return combined_audio if freqs else np.zeros(num_samples)

    def _generate_kick(self, duration_sec, sample_rate):
        num_samples = int(duration_sec * sample_rate); t = np.linspace(0, duration_sec, num_samples, False)
        pitch_env = np.geomspace(120, 40, num_samples); thump = np.sin(2 * np.pi * np.cumsum(pitch_env) / sample_rate)
        thump_env = np.exp(-25.0 * t)
        click_noise = np.random.uniform(-1, 1, num_samples)
        b, a = signal.butter(2, 2000/(0.5*sample_rate), btype='high'); filtered_click = signal.lfilter(b, a, click_noise)
        click_env = np.exp(-200.0 * t)
        return (thump * thump_env * 0.9) + (filtered_click * click_env * 0.1)

    def _generate_snare(self, duration_sec, sample_rate):
        num_samples = int(duration_sec * sample_rate); t = np.linspace(0, duration_sec, num_samples, False)
        body_tone = np.sin(2 * np.pi * 180 * t) + np.sin(2 * np.pi * 280 * t); body_env = np.exp(-30.0 * t)
        snap_noise = np.random.uniform(-1, 1, num_samples)
        b, a = signal.butter(4, 1500/(0.5*sample_rate), btype='high'); filtered_snap = signal.lfilter(b, a, snap_noise)
        snap_env = np.exp(-40.0 * t)
        return (body_tone * body_env * 0.3) + (filtered_snap * snap_env * 0.7)

    def _generate_hi_hat(self, duration_sec, sample_rate, is_open=False):
        num_samples = int(duration_sec * sample_rate)
        raw_sound = sum(signal.square(2 * np.pi * freq * np.linspace(0, duration_sec, num_samples, False)) for freq in [3000, 4700, 6800, 8500, 9800])
        b, a = signal.butter(6, 6000/(0.5*sample_rate), btype='high'); filtered_sound = signal.lfilter(b, a, raw_sound)
        env = np.exp(-(15.0 if is_open else 80.0) * np.linspace(0, duration_sec, num_samples, False))
        return filtered_sound * env

    def _generate_percussion_sound(self, drum_type, duration_sec, sample_rate):
        self.update_log(f"Generating percussion: {drum_type} for {duration_sec}s", 'debug', debug_only=True)
        if duration_sec <= 0: return np.zeros(0)
        if drum_type == 'kick': return self._generate_kick(duration_sec, sample_rate)
        elif drum_type == 'snare': return self._generate_snare(duration_sec, sample_rate)
        elif drum_type == 'hihat_closed': return self._generate_hi_hat(duration_sec, sample_rate, is_open=False)
        elif drum_type == 'hihat_open': return self._generate_hi_hat(duration_sec, sample_rate, is_open=True)
        elif drum_type == 'tom': return self._generate_tone(duration_sec, sample_rate, [120], 'Sine') * np.exp(-20.0 * np.linspace(0, duration_sec, int(duration_sec * sample_rate), False))
        elif drum_type == 'crash':
            noise = np.random.uniform(-1, 1, int(duration_sec * sample_rate))
            b, a = signal.butter(8, 4000/(0.5*sample_rate), btype='high')
            return signal.lfilter(b, a, noise) * np.exp(-4.0 * np.linspace(0, duration_sec, int(duration_sec * sample_rate), False))
        return np.zeros(int(duration_sec*sample_rate))

    def _generate_dynamic_drum_rhythm(self, section_name, section_duration, drum_bpm, song_style, tension):
        self.update_log(f"Generating drum rhythm for {section_name} (Tension: {tension:.2f})", 'debug', debug_only=True)
        drum_track_data = []; beat_duration = 60.0 / drum_bpm
        
        swing_factor = random.uniform(0.01, 0.08)
        humanization_factor = beat_duration * 0.05

        num_measures = int(section_duration / (beat_duration * 4))
        self.update_log(f"  -> Measures: {num_measures}, Beat Duration: {beat_duration:.3f}s", 'debug', debug_only=True)
        for measure in range(num_measures):
            is_fill_measure = (measure + 1) % 4 == 0 and random.random() < (0.15 + tension * 0.3)
            pattern = self.DRUM_PATTERNS[song_style]['fill' if is_fill_measure else 'main']
            self.update_log(f"  Measure {measure+1}: Using {'fill' if is_fill_measure else 'main'} pattern.", 'debug', debug_only=True)
            measure_start_time = measure * beat_duration * 4
            if measure % 4 == 0 and tension > 0.7 and random.random() < 0.6:
                drum_track_data.append({'start_time': measure_start_time, 'duration': beat_duration * 2, 'drum_type': 'crash', 'volume': 0.8})
                self.update_log(f"  -> Added tension crash at measure start.", 'debug', debug_only=True)
            for beat, drum_type in pattern:
                swing_delay = (beat_duration * swing_factor) if beat % 1.0 in [0.5, 0.75] else 0
                hit_time = max(0, measure_start_time + (beat * beat_duration) + swing_delay + random.uniform(-humanization_factor, humanization_factor))
                
                base_volume = 1.0 if beat % 4 == 0 else 0.85 if beat % 4 == 2 else 0.7
                final_volume = base_volume
                duration = beat_duration * 0.5 if 'open' in drum_type or 'crash' in drum_type else beat_duration * 0.25
                if hit_time < (measure + 1) * beat_duration * 4:
                    drum_track_data.append({'start_time': hit_time, 'duration': duration, 'drum_type': drum_type, 'volume': final_volume})
        return drum_track_data

    def _get_rhythm_sequence(self, total_beats, tension=0.5, exclude_motif=None, persistent_motif=None):
        sequence, beats_generated = [], 0
        
        if persistent_motif:
            chosen_motif_name = persistent_motif
            self.update_log(f"  Rhythm Gen: Using persistent motif '{chosen_motif_name}'", 'debug', debug_only=True)
        elif 0.3 < tension < 0.8 and random.random() < 0.25:
            chosen_motif_name = random.choice(list(self.POETIC_METERS.keys()))
            self.update_log(f"  Rhythm Gen: Using Poetic Meter '{chosen_motif_name}'", 'debug', debug_only=True)
        else:
            if tension > 0.7: motif_choices = ['syncopated', 'gallop', 'offbeat', 'triplet']
            elif tension > 0.4: motif_choices = ['straight', 'dotted', 'offbeat', 'triplet']
            else: motif_choices = ['straight', 'dotted']
            if exclude_motif and len(motif_choices) > 1: motif_choices = [m for m in motif_choices if m != exclude_motif]
            
            chosen_motif_name = random.choice(motif_choices)
            self.update_log(f"  Rhythm Gen: Total beats={total_beats}, Tension={tension:.2f}, Chosen Motif={chosen_motif_name}", 'debug', debug_only=True)

        if chosen_motif_name in self.POETIC_METERS:
            motif = self.POETIC_METERS[chosen_motif_name]
        else:
            motif = self.RHYTHMIC_MOTIFS[chosen_motif_name]

        while beats_generated < total_beats:
            for duration in motif:
                if beats_generated + duration > total_beats:
                    if total_beats - beats_generated > 0: sequence.append(total_beats - beats_generated)
                    beats_generated = total_beats; break
                sequence.append(duration); beats_generated += duration
            if beats_generated < total_beats and random.random() < 0.3 and beats_generated + 0.5 <= total_beats:
                sequence.append(-0.5); beats_generated += 0.5
        self.update_log(f"  -> Generated sequence: {sequence}", 'debug', debug_only=True)
        return [sequence], chosen_motif_name

    def _apply_schema(self, start_idx, schema_name, scale_notes, beat_duration):
        schema, events, current_time = self.CLASSICAL_SCHEMAS[schema_name], [], 0
        self.update_log(f"Applying classical schema: {schema_name}", 'main')
        for i, step in enumerate(schema['pattern']):
            current_step = step
            if random.random() < 0.15:
                alteration = random.choice([-2, 2])
                current_step += alteration
                self.update_log(f"  UID Alteration: Changed step {i} by {alteration}", 'debug', debug_only=True)

            note_idx = max(0, min(len(scale_notes) - 1, start_idx + current_step))
            duration = schema['durations'][i] * beat_duration
            
            events.append({'duration': duration, 'freqs': [scale_notes[note_idx]], 'scale_idx': [note_idx]})
            current_time += duration
        return events, current_time

    def _build_harmony_figure(self, base_note_idx, scale_len, base_scale_len, dissonance_level, current_chord_indices):
        num_notes = random.choices([1, 2, 3], weights=[0.7, 0.25, 0.05])[0]
        if num_notes == 1: return [base_note_idx]
        notes = [base_note_idx]
        octave_offset = (base_note_idx // base_scale_len) * base_scale_len
        chord_tones_in_octave = [idx + octave_offset for idx in current_chord_indices]
        for _ in range(num_notes - 1):
            new_note = random.choice(chord_tones_in_octave)
            if random.random() < 0.3: new_note += random.choice([-1, 1]) * base_scale_len
            new_note = max(0, min(scale_len - 1, new_note))
            if new_note not in notes: notes.append(new_note)
        return sorted(list(set(notes)))

    def _get_waveform(self, var):
        val = var.get()
        if val == "Random": 
            choice = random.choice(["Sine", "Piano", "Violin", "Cello", "Guitar", "Rich Saw", "Hollow Square"])
            self.update_log(f"Random waveform selected: {choice}", 'debug', debug_only=True)
            return choice
        return val
        
    def _generate_structural_melody(self, chord_progression_indices, base_scale_len):
        guide = [random.choice(chord_indices) + (base_scale_len * 2) if chord_indices else None for chord_indices in chord_progression_indices]
        self.update_log(f"Generated structural melody guide: {guide}", 'debug', debug_only=True)
        return guide

    def _apply_modal_interchange(self, progression, scale_type):
        if random.random() > 0.25 or scale_type not in self.MODAL_INTERCHANGE_MAP: return progression
        new_progression, interchange_options = progression[:], self.MODAL_INTERCHANGE_MAP[scale_type]
        eligible_indices = [i for i, chord in enumerate(new_progression) if chord in interchange_options]
        if eligible_indices:
            idx_to_change = random.choice(eligible_indices); original_chord = new_progression[idx_to_change]
            new_progression[idx_to_change] = interchange_options[original_chord]
            self.update_log(f"Modal Interchange: Changed {original_chord} to {new_progression[idx_to_change]}", 'main')
            self.update_log(f"  -> New progression: {new_progression}", 'debug', debug_only=True)
        return new_progression

    def _apply_neapolitan_chord(self, progression, scale_type, diatonic_chords):
        if random.random() > 0.3: return progression # Apply sparingly
        new_progression = progression[:]
        for i in range(len(new_progression) - 1):
            # Find a V chord that is preceded by a ii or iv
            is_V_chord = 'V' in new_progression[i+1] or 'v' in new_progression[i+1]
            is_precadential = 'ii' in new_progression[i] or 'iv' in new_progression[i]
            if is_V_chord and is_precadential:
                original_chord = new_progression[i]
                new_progression[i] = 'bII'
                self.update_log(f"Harmonic Enrichment: Replaced {original_chord} with Neapolitan (bII) before {new_progression[i+1]}", 'main')
                return new_progression
        return progression

    def _apply_augmented_sixth_chords(self, progression, scale_type, diatonic_chords):
        if random.random() > 0.3: return progression
        new_progression = progression[:]
        for i in range(len(new_progression) - 1):
            is_V_chord = 'V' in new_progression[i+1] or 'v' in new_progression[i+1]
            # Aug6 chords typically resolve to V and often replace iv or VI
            is_replaceable = 'iv' in new_progression[i] or 'VI' in new_progression[i]
            if is_V_chord and is_replaceable:
                original_chord = new_progression[i]
                aug_type = random.choice(['It+6', 'Fr+6', 'Ger+6'])
                new_progression[i] = aug_type
                self.update_log(f"Harmonic Enrichment: Replaced {original_chord} with {aug_type} chord before {new_progression[i+1]}", 'main')
                return new_progression
        return progression

    def _generate_thematic_seed(self):
        num_notes, self.thematic_seed, last_interval = random.randint(3, 5), [], 0
        for _ in range(num_notes):
            interval = random.choice([-2, -1, -1, 1, 1, 2, 3])
            if interval == -last_interval and abs(last_interval) > 1: pass
            elif interval == 0: interval = random.choice([-1, 1])
            self.thematic_seed.append({'interval': interval, 'duration': random.choice([0.25, 0.5, 0.5, 1.0])}); last_interval = interval
        self.update_log(f"Generated thematic seed: {self.thematic_seed}", 'debug', debug_only=True)

    def _transform_and_apply_seed(self, start_idx, start_time, beat_duration, scale, waveform, volume):
        if not self.thematic_seed: return [], start_idx, start_time
        events, current_idx, current_time = [], start_idx, start_time
        transformation = random.choice(['none', 'inversion', 'augmentation', 'diminution', 'retrograde', 'sequence_up', 'sequence_down', 'fragmentation'])
        self.update_log(f"Applying thematic seed with transformation: {transformation}", "debug", debug_only=True)
        seed_to_use = copy.deepcopy(self.thematic_seed)
        if transformation == 'retrograde': seed_to_use.reverse()
        elif transformation == 'sequence_up': current_idx += 2
        elif transformation == 'sequence_down': current_idx -= 2
        elif transformation == 'fragmentation': seed_to_use = seed_to_use[:random.randint(1, len(seed_to_use)-1)]
        for note in seed_to_use:
            interval, duration = note['interval'], note['duration']
            if transformation == 'inversion': interval *= -1
            elif transformation == 'augmentation': duration *= 2
            elif transformation == 'diminution': duration /= 2
            current_idx = max(0, min(len(scale) - 1, current_idx + interval))
            events.append({'start_time': current_time, 'duration': duration * beat_duration, 'freqs': [scale[current_idx]], 'scale_idx': [current_idx], 'articulation': 1.0, 'volume': volume, 'waveform': waveform})
            current_time += duration * beat_duration
        return events, current_idx, current_time
    
    def _apply_cadence(self, progression, scale_type):
        if len(progression) < 3 or random.random() < 0.2: return progression
        new_prog = progression[:-2]
        is_major_scale = any(major_name in scale_type for major_name in self.MAJOR_LIKE_SCALES)
        cadence = ['V', 'I'] if is_major_scale else ['v', 'i']
        new_prog.extend(cadence)
        self.update_log(f"Applied cadence to progression, ending with {cadence}", 'debug', debug_only=True)
        return new_prog

    def _apply_voice_leading(self, last_chord_indices, current_chord_indices, base_scale_len):
        if not last_chord_indices or not current_chord_indices:
            return current_chord_indices
        
        new_chord_indices = []
        for target_note in current_chord_indices:
            min_dist, best_note = float('inf'), target_note
            for last_note in last_chord_indices:
                octave_multiple = round((last_note - target_note) / base_scale_len)
                candidate_note = target_note + (octave_multiple * base_scale_len)
                dist = abs(candidate_note - last_note)
                if dist < min_dist:
                    min_dist, best_note = dist, candidate_note
            new_chord_indices.append(best_note)
        
        self.update_log(f"  Initial voice leading result: {new_chord_indices}", 'debug', debug_only=True)

        if len(new_chord_indices) > 1:
            final_indices = []
            for idx in new_chord_indices:
                adjusted_idx = idx
                while adjusted_idx < 0:
                    adjusted_idx += base_scale_len
                final_indices.append(adjusted_idx)
            final_indices = sorted(list(set(final_indices)))
            
            if final_indices != sorted(list(set(new_chord_indices))):
                 self.update_log(f"  After normalizing negative indices: {final_indices}", 'debug', debug_only=True)

            while final_indices[-1] - final_indices[0] > base_scale_len:
                self.update_log(f"  Voicing constraint check on {final_indices}. Range ({final_indices[-1] - final_indices[0]}) > Max Range ({base_scale_len}). Tightening...", 'debug', debug_only=True)
                center_note = sum(final_indices) / len(final_indices)
                lowest_note = final_indices[0]
                highest_note = final_indices[-1]

                if abs(highest_note - center_note) > abs(lowest_note - center_note):
                    original_note_for_log = highest_note
                    final_indices[-1] -= base_scale_len
                    self.update_log(f"    -> Pulled down high note {original_note_for_log} to {final_indices[-1]}. New chord: {sorted(final_indices)}", 'debug', debug_only=True)
                else:
                    original_note_for_log = lowest_note
                    final_indices[0] += base_scale_len
                    self.update_log(f"    -> Pulled up low note {original_note_for_log} to {final_indices[0]}. New chord: {sorted(final_indices)}", 'debug', debug_only=True)
                
                final_indices.sort()
        else:
            final_indices = new_chord_indices

        final_indices = sorted(list(set(final_indices)))
        self.update_log(f"Voice leading: {last_chord_indices} -> {current_chord_indices} became {final_indices}", 'debug', debug_only=True)
        return final_indices

    def _apply_melodic_embellishments(self, melody_events, scale_notes, beat_duration, tension, song_affect, chord_progression_indices):
        if tension < 0.4: return melody_events, []
        
        ornamented_events, ornament_times = [], []
        self.update_log(f"Applying melodic embellishments with tension {tension:.2f} and affect {song_affect}", 'debug', debug_only=True)
        
        for i, event in enumerate(melody_events):
            ornamented_events.append(event)
            if not event.get('scale_idx'): continue
            
            main_note_idx = event['scale_idx'][0]
            is_strong_beat = (event['start_time'] % beat_duration) < 0.1 

            ornament_choices = ['acciaccatura', 'mordent']
            if event['duration'] >= beat_duration * 0.9: ornament_choices.append('turn')
            if event['duration'] >= beat_duration and song_affect != 'melancholy': ornament_choices.append('arpeggio_run')
            if is_strong_beat and song_affect != 'melancholy': ornament_choices.extend(['approach_note', 'enclosure'])

            if not ornament_choices or random.random() > (tension - 0.3): continue

            ornament_type = random.choice(ornament_choices)
            
            if ornament_type == 'arpeggio_run':
                current_chord_indices = []
                event_time_in_beats = event['start_time'] / beat_duration
                chord_index = int(event_time_in_beats / (len(melody_events) / len(chord_progression_indices))) % len(chord_progression_indices) if chord_progression_indices else 0
                if chord_progression_indices and chord_index < len(chord_progression_indices):
                    current_chord_indices = chord_progression_indices[chord_index]

                if not current_chord_indices: continue
                
                self.update_log(f"  -> Adding arpeggio run at {event['start_time']:.2f}s", 'debug', debug_only=True)
                ornamented_events.pop() 
                
                arp_pattern = [0, 2, 4, 2] 
                rhythm = self.ARPEGGIO_RHYTHMS[random.choice(list(self.ARPEGGIO_RHYTHMS.keys()))]
                
                time_cursor = event['start_time']
                
                for j, dur_factor in enumerate(rhythm):
                    note_dur = dur_factor * beat_duration
                    if time_cursor + note_dur > event['start_time'] + event['duration']:
                        note_dur = (event['start_time'] + event['duration']) - time_cursor
                    if note_dur < 0.01: continue

                    arp_note_base_idx = current_chord_indices[arp_pattern[j % len(arp_pattern)] % len(current_chord_indices)]
                    octave_multiple = round((main_note_idx - arp_note_base_idx) / 7)
                    arp_note_idx = max(0, min(len(scale_notes) - 1, arp_note_base_idx + (octave_multiple * 7)))

                    new_event = copy.deepcopy(event)
                    new_event.update({'start_time': time_cursor, 'duration': note_dur, 'scale_idx': [arp_note_idx], 'freqs': [scale_notes[arp_note_idx]]})
                    ornamented_events.append(new_event)
                    time_cursor += note_dur
                ornament_times.append(event['start_time'])

            elif ornament_type == 'acciaccatura' and main_note_idx > 0 and event['duration'] > 0.05:
                self.update_log(f"  -> Adding acciaccatura at {event['start_time']:.2f}s", 'debug', debug_only=True)
                event['duration'] -= 0.05; event['start_time'] += 0.05
                grace_event = copy.deepcopy(event)
                grace_event.update({'start_time': event['start_time'] - 0.05, 'duration': 0.05, 'scale_idx': [main_note_idx - 1], 'freqs': [scale_notes[main_note_idx - 1]]})
                ornamented_events.insert(-1, grace_event); ornament_times.append(grace_event['start_time'])
            
            elif ornament_type == 'mordent' and 0 < main_note_idx < len(scale_notes) - 1:
                ornament_dur = min(event['duration'] / 2, beat_duration / 4)
                if event['duration'] > ornament_dur * 2:
                    self.update_log(f"  -> Adding mordent at {event['start_time']:.2f}s", 'debug', debug_only=True)
                    event['duration'] -= ornament_dur; neighbor_idx = main_note_idx + random.choice([-1, 1])
                    mordent_note = copy.deepcopy(event); mordent_note.update({'duration': ornament_dur / 2, 'scale_idx': [neighbor_idx], 'freqs': [scale_notes[neighbor_idx]]})
                    return_note = copy.deepcopy(event); return_note.update({'start_time': event['start_time'] + ornament_dur/2, 'duration': ornament_dur/2})
                    ornamented_events.insert(-1, mordent_note); ornamented_events.insert(-1, return_note); ornament_times.append(event['start_time'])
            elif ornament_type == 'turn' and 0 < main_note_idx < len(scale_notes) - 1:
                turn_duration = min(event['duration'], beat_duration / 2)
                if event['duration'] > turn_duration:
                    self.update_log(f"  -> Adding turn at {event['start_time']:.2f}s", 'debug', debug_only=True)
                    event['start_time'] += turn_duration; event['duration'] -= turn_duration
                    note_dur = turn_duration / 4
                    turn_indices = [main_note_idx + 1, main_note_idx, main_note_idx - 1, main_note_idx]
                    for j, turn_idx in enumerate(turn_indices):
                        turn_note = copy.deepcopy(event)
                        turn_note.update({'start_time': event['start_time'] - turn_duration + (j * note_dur), 'duration': note_dur, 'scale_idx': [turn_idx], 'freqs': [scale_notes[turn_idx]]})
                        ornamented_events.insert(-1, turn_note)
                    ornament_times.append(event['start_time'] - turn_duration)

        return ornamented_events, ornament_times

    def _map_chord_to_polytonal_scale(self, original_chord_indices, original_scale_notes, polytonal_scale_notes):
        return [polytonal_scale_notes.index(min(polytonal_scale_notes, key=lambda f: abs(f - original_scale_notes[idx]))) for idx in original_chord_indices]

    def _generate_rhythmic_chord_events(self, start_time, duration, chord_indices_voic_led, scale_notes, base_scale_len, beat_duration, tension, waveform, song_affect, volume_multiplier=1.0):
        events = []
        num_beats = round(duration / beat_duration)
        if num_beats < 1: return []

        style_weights = {'held': 0.8 - tension * 0.7, 'comping': tension * 0.8, 'arpeggiated': tension * 0.6}
        if song_affect == 'melancholy':
            style_weights['arpeggiated'] *= 0.1

        total_weight = sum(style_weights.values())
        if total_weight <= 0: chosen_style = 'held'
        else:
            style_weights = {k: v / total_weight for k, v in style_weights.items()}
            chosen_style = random.choices(list(style_weights.keys()), weights=list(style_weights.values()), k=1)[0]
        
        self.update_log(f"    Chord Style: {chosen_style} for {num_beats} beats (Affect: {song_affect})", 'debug', debug_only=True)
        chord_freqs = [scale_notes[idx] for idx in chord_indices_voic_led]
        volume = (0.5 + tension * 0.3) * volume_multiplier

        if chosen_style == 'held' or num_beats < 2:
            events.append({'start_time': start_time, 'duration': duration, 'freqs': chord_freqs, 'volume': volume, 'articulation': 1.0, 'waveform': waveform})
        
        elif chosen_style == 'comping':
            patterns = {
                'pop': [(0, 1), (1.5, 0.5), (2.5, 0.5)], 'push': [(0.5, 0.5), (1.5, 0.5), (2.5, 0.5), (3.5, 0.5)], 'standard': [(0, 1), (2, 1)]
            }
            pattern = random.choice(list(patterns.values()))
            beats_covered = 0
            while beats_covered < num_beats:
                for beat_offset, dur_in_beats in pattern:
                    if beats_covered + beat_offset >= num_beats: continue
                    event_start = start_time + (beats_covered + beat_offset) * beat_duration
                    event_dur = min(dur_in_beats * beat_duration, duration - (event_start - start_time))
                    if event_dur > 0.01:
                        events.append({'start_time': event_start, 'duration': event_dur, 'freqs': chord_freqs, 'volume': volume, 'articulation': 1.0, 'waveform': waveform})
                beats_covered += 4
        
        elif chosen_style == 'arpeggiated':
            rhythm_pattern = self.ARPEGGIO_RHYTHMS[random.choice(list(self.ARPEGGIO_RHYTHMS.keys()))]
            time_cursor = start_time
            arp_notes = [scale_notes[idx] for idx in chord_indices_voic_led]
            arp_pattern_indices = [0, 1, 2, 1] 
            
            beat_num = 0
            while time_cursor < start_time + duration:
                note_dur = rhythm_pattern[beat_num % len(rhythm_pattern)] * beat_duration
                if time_cursor + note_dur > start_time + duration:
                    note_dur = (start_time + duration) - time_cursor
                if note_dur < 0.01: break
                
                note_freq = arp_notes[arp_pattern_indices[beat_num % len(arp_pattern_indices)] % len(arp_notes)]
                events.append({'start_time': time_cursor, 'duration': note_dur, 'freqs': [note_freq], 'volume': volume, 'articulation': 0.9, 'waveform': waveform})
                time_cursor += note_dur
                beat_num += 1

        return events

    def _generate_rhythmic_bass_events(self, start_time, duration, chord_indices, next_chord_indices, scale_notes, base_scale_len, beat_duration, tension, waveform, melody_events, song_affect, volume_multiplier=1.0):
        events = []
        num_beats = round(duration / beat_duration)
        if num_beats < 1 or not chord_indices: return []

        style_weights = {'held': 0.2 - tension * 0.2, 'arpeggiated': tension * 0.8, 'walking': tension * 1.5, 'rhythmic': tension * 0.5}
        if song_affect == 'melancholy':
            style_weights['arpeggiated'] *= 0.1 
            style_weights['walking'] *= 0.5

        total_weight = sum(style_weights.values())
        if total_weight <= 0: chosen_style = 'held'
        else:
            style_weights = {k: v / total_weight for k, v in style_weights.items()}
            chosen_style = random.choices(list(style_weights.keys()), weights=list(style_weights.values()), k=1)[0]
        
        self.update_log(f"    Bass Style: {chosen_style} for {num_beats} beats (Affect: {song_affect})", 'debug', debug_only=True)
        volume = (0.7 + tension * 0.3) * volume_multiplier
        octave_shift = base_scale_len * 2
        
        def safe_get_note(idx):
            return max(0, min(len(scale_notes) - 1, idx))

        root_note_idx = safe_get_note(chord_indices[0] - octave_shift)
        
        if chosen_style == 'walking' and num_beats >= 2:
            current_note = root_note_idx
            notes_to_play = [current_note]
            chord_tones_in_octave = [safe_get_note(idx - octave_shift) for idx in chord_indices]
            target_note = safe_get_note(next_chord_indices[0] - octave_shift) if next_chord_indices else root_note_idx

            for beat in range(1, int(num_beats)):
                last_note = notes_to_play[-1]
                is_strong_beat = (beat % 2 == 0)
                
                if is_strong_beat:
                    possible_targets = [ct for ct in chord_tones_in_octave if ct != last_note] or chord_tones_in_octave
                    next_note = random.choice(possible_targets)
                else:
                    next_chord_tone_target = min(chord_tones_in_octave, key=lambda x: abs(x - (last_note + np.sign(random.random() - 0.5))))
                    direction = np.sign(next_chord_tone_target - last_note)
                    if direction != 0: next_note = last_note + direction
                    else: next_note = last_note + random.choice([-1, 1])

                current_note = safe_get_note(next_note)
                notes_to_play.append(current_note)

            for beat, note_idx in enumerate(notes_to_play):
                event_start = start_time + beat * beat_duration
                event_dur = min(beat_duration, duration - (event_start - start_time))
                if event_dur > 0.01:
                    freq = scale_notes[safe_get_note(note_idx)]
                    events.append({'start_time': event_start, 'duration': event_dur, 'freqs': [freq], 'volume': volume, 'articulation': 1.0, 'waveform': waveform})

        elif chosen_style == 'arpeggiated' and len(chord_indices) >= 2:
            arp_notes = [safe_get_note(idx - octave_shift) for idx in chord_indices]
            if len(arp_notes) > 1: arp_notes.append(safe_get_note(chord_indices[0] - octave_shift + base_scale_len))
            pattern_choice = random.choice(['up', 'down', 'up-down', 'random'])
            if pattern_choice == 'down': arp_notes.reverse()
            elif pattern_choice == 'up-down': arp_notes = arp_notes + arp_notes[-2::-1]
            
            rhythm_pattern = self.ARPEGGIO_RHYTHMS[random.choice(['eighths', 'swing', 'dotted'])]
            time_cursor = start_time
            beat_num = 0
            while time_cursor < start_time + duration:
                note_dur = rhythm_pattern[beat_num % len(rhythm_pattern)] * beat_duration
                if time_cursor + note_dur > start_time + duration:
                    note_dur = (start_time + duration) - time_cursor
                if note_dur < 0.01: break
                
                note_idx = random.choice(arp_notes) if pattern_choice == 'random' else arp_notes[beat_num % len(arp_notes)]
                events.append({'start_time': time_cursor, 'duration': note_dur, 'freqs': [scale_notes[note_idx]], 'volume': volume, 'articulation': 1.0, 'waveform': waveform})
                time_cursor += note_dur
                beat_num += 1

        elif chosen_style == 'rhythmic':
            notes_to_use = [safe_get_note(idx - octave_shift) for idx in chord_indices]
            melodic_rhythm = []
            if melody_events:
                chord_end_time = start_time + duration
                for event in melody_events:
                    if start_time <= event['start_time'] < chord_end_time:
                        relative_start = (event['start_time'] - start_time) / beat_duration
                        melodic_rhythm.append(relative_start)
            if not melodic_rhythm or random.random() < 0.3: melodic_rhythm = [b for b in range(num_beats)]
            
            for beat_start in melodic_rhythm:
                event_start = start_time + beat_start * beat_duration
                if event_start >= start_time + duration: continue
                note_idx = random.choice(notes_to_use)
                events.append({'start_time': event_start, 'duration': beat_duration * 0.9, 'freqs': [scale_notes[note_idx]], 'volume': volume, 'articulation': 0.9, 'waveform': waveform})

        else: # Fallback to 'held'
            bass_note_idx = root_note_idx
            if len(chord_indices) >= 3 and random.random() < 0.2: bass_note_idx = safe_get_note(random.choice(chord_indices[1:]) - octave_shift)
            events.append({'start_time': start_time, 'duration': duration, 'freqs': [scale_notes[bass_note_idx]], 'volume': volume, 'articulation': 1.0, 'waveform': waveform})

        return events

    def _apply_secondary_dominants(self, progression, scale_type):
        if len(progression) < 2:
            return progression
        
        new_progression = []
        for i in range(len(progression) - 1):
            new_progression.append(progression[i])
            
            current_chord = progression[i]
            next_chord = progression[i+1]
            
            is_valid_target = (next_chord.islower() or next_chord.isupper()) and 'i' not in next_chord.lower()
            
            if is_valid_target and random.random() < 0.35:
                secondary_dominant = f"V7/{next_chord}"
                new_progression.append(secondary_dominant)
                self.update_log(f"Harmonic Enrichment: Added secondary dominant {secondary_dominant} before {next_chord}", 'main')
        
        new_progression.append(progression[-1])
        
        if len(new_progression) > len(progression):
             self.update_log(f"  -> New progression: {new_progression}", 'debug', debug_only=True)
             
        return new_progression

    def _apply_secondary_leading_tones(self, progression, scale_type):
        if len(progression) < 2 or random.random() < 0.7:
            return progression
        
        new_progression = []
        for i in range(len(progression) - 1):
            new_progression.append(progression[i])
            
            next_chord = progression[i+1]
            
            is_valid_target = (next_chord.islower() or next_chord.isupper()) and 'i' not in next_chord.lower()
            
            if is_valid_target and random.random() < 0.2:
                secondary_lt = f"vii°7/{next_chord}"
                new_progression.append(secondary_lt)
                self.update_log(f"Harmonic Enrichment: Added secondary leading-tone {secondary_lt} before {next_chord}", 'main')

        new_progression.append(progression[-1])
        
        if len(new_progression) > len(progression):
             self.update_log(f"  -> New progression: {new_progression}", 'debug', debug_only=True)
             
        return new_progression

    def _get_chord_indices_from_roman(self, roman_numeral, scale_type, key_root_note):
        # This is the new, rewritten function
        diatonic_chords_for_scale = self.DIATONIC_CHORDS.get(scale_type, {})
        base_scale_len = len(self.INTERVAL_NAMES.get(scale_type, []))
        
        # Handle secondary dominants/leading tones (e.g., "V7/V", "vii°7/ii")
        if "/" in roman_numeral:
            try:
                secondary_chord_part, target_roman = roman_numeral.split('/', 1)
                
                target_degree = self.ROMAN_TO_DEGREE.get(target_roman.lower())
                if target_degree is None: return []

                primary_scale_intervals = self.INTERVAL_NAMES.get(scale_type, self.MAJOR_INTERVALS)
                if target_degree >= len(primary_scale_intervals): return []

                target_root_semitone_offset = primary_scale_intervals[target_degree]
                
                quality_intervals = []
                if "V" in secondary_chord_part:
                    quality_intervals = self.CHORD_QUALITIES['dom7'] if '7' in secondary_chord_part else self.CHORD_QUALITIES['maj']
                elif "vii" in secondary_chord_part:
                    quality_intervals = self.CHORD_QUALITIES['half-dim7'] if '7' in secondary_chord_part else self.CHORD_QUALITIES['dim']
                else:
                    return []

                chord_semitones = [(target_root_semitone_offset + interval) % 12 for interval in quality_intervals]

                chord_indices = []
                for semitone in chord_semitones:
                    closest_degree, min_dist = -1, float('inf')
                    for i, scale_interval in enumerate(primary_scale_intervals):
                        dist = min(abs(semitone - scale_interval), 12 - abs(semitone - scale_interval))
                        if dist < min_dist:
                            min_dist = dist
                            closest_degree = i
                    if closest_degree != -1:
                        chord_indices.append(closest_degree)

                return sorted(list(set(chord_indices)))

            except Exception as e:
                self.update_log(f"Error parsing secondary chord '{roman_numeral}': {e}", 'debug', debug_only=True)
                return []
        
        # Handle Neapolitan and Augmented Sixth
        elif roman_numeral == 'bII':
            # Major triad on the lowered supertonic
            b2_degree = (self.ROMAN_TO_DEGREE['ii'] - 1 + base_scale_len) % base_scale_len
            return [b2_degree, (b2_degree + 4) % base_scale_len, (b2_degree + 7) % base_scale_len]
        elif '+6' in roman_numeral:
            # These are complex chromatic chords, based on the lowered 6th degree
            b6_degree = (self.ROMAN_TO_DEGREE['vi'] - 1 + base_scale_len) % base_scale_len
            if 'It' in roman_numeral: # Italian
                return [b6_degree, self.ROMAN_TO_DEGREE['i'], (self.ROMAN_TO_DEGREE['iv'] + 1) % base_scale_len]
            elif 'Fr' in roman_numeral: # French
                return [b6_degree, self.ROMAN_TO_DEGREE['i'], self.ROMAN_TO_DEGREE['ii'], (self.ROMAN_TO_DEGREE['iv'] + 1) % base_scale_len]
            elif 'Ger' in roman_numeral: # German
                return [b6_degree, self.ROMAN_TO_DEGREE['i'], self.ROMAN_TO_DEGREE['iii']-1, (self.ROMAN_TO_DEGREE['iv'] + 1) % base_scale_len]


        else:
            if roman_numeral in diatonic_chords_for_scale:
                return diatonic_chords_for_scale[roman_numeral]
            
            cleaned_roman = roman_numeral.replace('°', '').replace('+', '').replace('7', '')
            for chord, indices in diatonic_chords_for_scale.items():
                if chord.replace('°', '').replace('+', '').replace('7', '') == cleaned_roman:
                    return indices

            self.update_log(f"Warning: Could not find chord '{roman_numeral}' in {scale_type}. Using tonic.", 'debug', debug_only=True)
            return diatonic_chords_for_scale.get('I', diatonic_chords_for_scale.get('i', []))

    def _generate_song_section_data(self, selected_scale_name, selected_scale_notes, scale_type, progression_name, section_duration, melody_bpm, log_callback, scale_notes_base, texture_mode, song_affect, tension=0.5, is_heterophonic=False, is_reprise=False, is_polyrhythmic=False, is_polytonal=False, section_profile={}, urlinie_segment=None, pitch_class_set=None):
        log_callback(f"Generating section data for '{progression_name}' with affect '{song_affect}'", 'debug', debug_only=True)
        progression_romans_base = self.CHORD_PROGRESSIONS.get(scale_type, {}).get(progression_name, [])
        if not progression_romans_base:
            log_callback(f"No '{progression_name}' progression for {scale_type}. Using fallback.", 'debug', debug_only=True)
            progression_romans_base = ['i', 'iv', 'v', 'i'] if scale_type in self.MINOR_LIKE_SCALES else ['I', 'IV', 'V', 'I']
        
        progression_romans_themed = self._apply_modal_interchange(progression_romans_base, scale_type)
        progression_romans_secondary = self._apply_secondary_dominants(progression_romans_themed, scale_type)
        progression_romans_lt = self._apply_secondary_leading_tones(progression_romans_secondary, scale_type)
        progression_romans_neapolitan = self._apply_neapolitan_chord(progression_romans_lt, scale_type, self.DIATONIC_CHORDS)
        progression_romans_aug6 = self._apply_augmented_sixth_chords(progression_romans_neapolitan, scale_type, self.DIATONIC_CHORDS)
        progression_romans = self._apply_cadence(progression_romans_aug6, scale_type)

        log_callback(f"Progression for {progression_name.title()}: {progression_romans} (Texture: {texture_mode})", 'main')

        key_root_note = selected_scale_name.split(' ')[0]
        chord_progression_indices_base = [self._get_chord_indices_from_roman(r, scale_type, key_root_note) for r in progression_romans]

        melody1_events, melody2_events, bass_events, chord_events = [], [], [], []
        base_scale_len = len(scale_notes_base)
        
        if urlinie_segment is None:
            structural_melody_guide = self._generate_structural_melody(chord_progression_indices_base, base_scale_len)
        else:
            structural_melody_guide = urlinie_segment

        characteristic_note_idx = self.MODAL_CHARACTERISTICS.get(scale_type)
        initial_chord_note_m1 = chord_progression_indices_base[0][0] if chord_progression_indices_base and chord_progression_indices_base[0] else 0
        m1_current_idx = m1_last_idx = initial_chord_note_m1 + base_scale_len * 2
        m2_current_idx = m2_last_idx = m1_last_idx - base_scale_len
        beat_duration = 60.0 / melody_bpm
        chord_duration = section_duration / len(chord_progression_indices_base) if chord_progression_indices_base else section_duration
        current_time, last_chord_indices_voic_led = 0.0, []

        m1_vol_mult = section_profile.get('m1_vol', 1.0)
        m2_vol_mult = section_profile.get('m2_vol', 1.0)
        bass_vol_mult = section_profile.get('bass_vol', 1.0)
        chords_vol_mult = section_profile.get('chords_vol', 1.0)

        polytonal_scale_notes = selected_scale_notes
        if is_polytonal:
            related_key = self._get_related_key(selected_scale_name, 'dominant')
            polytonal_scale_base = self.MUSICAL_SCALES[related_key]
            polytonal_scale_notes = [f/2 for f in polytonal_scale_base] + polytonal_scale_base + [f*2 for f in polytonal_scale_base] + [f*4 for f in polytonal_scale_base]
            log_callback(f"Melody 2 uses polytonal key: {related_key}", 'debug', debug_only=True)
        
        _, section_rhythmic_motif = self._get_rhythm_sequence(16, tension=tension)

        for i, chord_indices in enumerate(chord_progression_indices_base):
            if not chord_indices:
                self.update_log(f"Skipping unresolved chord '{progression_romans[i]}'", "debug", debug_only=True)
                current_time += chord_duration
                continue

            log_callback(f"  Processing chord {i+1}/{len(chord_progression_indices_base)}: {progression_romans[i]}", 'debug', debug_only=True)
            chord_indices_voic_led = self._apply_voice_leading(last_chord_indices_voic_led, chord_indices, base_scale_len)
            last_chord_indices_voic_led = chord_indices_voic_led
            target_structural_note = structural_melody_guide[i] if i < len(structural_melody_guide) else None
            num_chord_beats = int(round(chord_duration / beat_duration))
            time_m1, m1_events_this_chord = current_time, []
            
            if m1_vol_mult > 0:
                rhythm_phrases_m1, _ = self._get_rhythm_sequence(num_chord_beats, tension=tension * (1.2 if is_reprise else 1.0), persistent_motif=section_rhythmic_motif)
                beats_elapsed = 0
                for phrase in rhythm_phrases_m1:
                    contour = random.choice(['rising', 'falling', 'arch', 'valley'])
                    for beat in phrase:
                        duration = abs(beat) * beat_duration
                        if time_m1 >= current_time + chord_duration: continue
                        if beat > 0:
                            phrase_progress = beats_elapsed / sum(abs(b) for p in rhythm_phrases_m1 for b in p) if sum(abs(b) for p in rhythm_phrases_m1 for b in p) > 0 else 0
                            m1_new_idx, _, _ = self._generate_melodic_note(m1_current_idx, m1_last_idx, selected_scale_notes, chord_indices, 0, 0, scale_type, log_callback, contour, phrase_progress, tension=tension, target_note_idx=target_structural_note, characteristic_note_idx=characteristic_note_idx, pitch_class_set=pitch_class_set)
                            m1_figure = self._build_harmony_figure(m1_new_idx, len(selected_scale_notes), base_scale_len, 0.1, chord_indices)
                            volume = (0.6 + tension * 0.4) * m1_vol_mult
                            m1_events_this_chord.append({'start_time': time_m1, 'duration': duration, 'freqs': [selected_scale_notes[i] for i in m1_figure], 'scale_idx': m1_figure, 'articulation': 1.0, 'volume': volume, 'waveform': self.current_m1_waveform})
                            m1_current_idx = m1_new_idx
                        time_m1 += duration; beats_elapsed += abs(beat)

            m1_events_this_chord, m1_ornament_times = self._apply_melodic_embellishments(m1_events_this_chord, selected_scale_notes, beat_duration, tension, song_affect, chord_progression_indices_base)
            melody1_events.extend(m1_events_this_chord)
            
            if m2_vol_mult > 0:
                if texture_mode == 'counterpoint':
                    counterpoint_engine = SpeciesCounterpointEngine(m1_events_this_chord, selected_scale_notes, base_scale_len)
                    melody2_events.extend(counterpoint_engine.generate_first_species(m2_current_idx, self.current_m2_waveform, m2_vol_mult))
                elif is_heterophonic:
                    for event in m1_events_this_chord:
                        if 'scale_idx' not in event or not event['scale_idx']: continue
                        new_event = copy.deepcopy(event)
                        if is_polyrhythmic and random.random() < 0.4 and new_event['duration'] > beat_duration * 0.4:
                            new_event['duration'] /= 2; second_note_event = copy.deepcopy(new_event); second_note_event['start_time'] += new_event['duration']; melody2_events.append(second_note_event)
                        if is_polytonal:
                            closest_poly_freq = min(polytonal_scale_notes, key=lambda f: abs(f - selected_scale_notes[new_event['scale_idx'][0]])); new_event['scale_idx'] = [polytonal_scale_notes.index(closest_poly_freq)]; new_event['freqs'] = [closest_poly_freq]
                        new_event['volume'] *= (0.7 * m2_vol_mult); new_event['waveform'] = self.current_m2_waveform; melody2_events.append(new_event)
            
            next_chord_indices = None
            if i + 1 < len(chord_progression_indices_base):
                next_chord_roman = progression_romans[i+1]
                next_chord_indices = self._get_chord_indices_from_roman(next_chord_roman, scale_type, key_root_note)
            
            if bass_vol_mult > 0:
                bass_events.extend(self._generate_rhythmic_bass_events(
                    start_time=current_time, duration=chord_duration,
                    chord_indices=chord_indices_voic_led, next_chord_indices=next_chord_indices,
                    scale_notes=selected_scale_notes, base_scale_len=base_scale_len,
                    beat_duration=beat_duration, tension=tension, waveform=self.current_bass_waveform,
                    melody_events=m1_events_this_chord, song_affect=song_affect, volume_multiplier=bass_vol_mult
                ))
            
            if chords_vol_mult > 0 and pitch_class_set is None:
                chord_events.extend(self._generate_rhythmic_chord_events(
                    start_time=current_time, duration=chord_duration,
                    chord_indices_voic_led=chord_indices_voic_led, scale_notes=selected_scale_notes,
                    base_scale_len=base_scale_len, beat_duration=beat_duration, tension=tension,
                    waveform=self.current_chord_waveform, song_affect=song_affect, volume_multiplier=chords_vol_mult
                ))

            current_time += chord_duration
        return {'melody1': melody1_events, 'melody2': melody2_events, 'bass': bass_events, 'chords': chord_events}

    def _generate_outro_section_data(self, selected_scale_name, selected_scale_notes, scale_type, section_duration, melody_bpm, log_callback, scale_notes_base, song_affect):
        log_callback("Generating specialized outro section...", 'debug', debug_only=True)
        melody1_events, bass_events, chord_events = [], [], []
        base_scale_len = len(scale_notes_base)
        beat_duration = 60.0 / melody_bpm
        
        def safe_get_note(idx):
            return max(0, min(len(scale_notes) - 1, idx))

        if song_affect in ['melancholy', 'serene']:
            progression_romans = ['iv', 'v', 'i', 'i'] if scale_type in self.MINOR_LIKE_SCALES else ['IV', 'V', 'I', 'I']
            log_callback(f"Outro Progression: {progression_romans}", 'main')
            key_root_note = selected_scale_name.split(' ')[0]
            chord_progression_indices_base = [self._get_chord_indices_from_roman(r, scale_type, key_root_note) for r in progression_romans]
            chord_duration = section_duration / len(chord_progression_indices_base) if chord_progression_indices_base else section_duration
            m1_current_idx = (chord_progression_indices_base[0][0] if chord_progression_indices_base and chord_progression_indices_base[0] else 0) + base_scale_len * 2
            current_time, last_chord_indices_voic_led = 0.0, []

            for i, chord_indices in enumerate(chord_progression_indices_base):
                if not chord_indices: continue
                chord_indices_voic_led = self._apply_voice_leading(last_chord_indices_voic_led, chord_indices, base_scale_len)
                last_chord_indices_voic_led = chord_indices_voic_led
                
                melody1_events.append({'start_time': current_time, 'duration': chord_duration, 'freqs': [selected_scale_notes[m1_current_idx]], 'scale_idx': [m1_current_idx], 'articulation': 1.0, 'volume': 0.5, 'waveform': self.current_m1_waveform})
                if i + 1 < len(chord_progression_indices_base) and chord_progression_indices_base[i+1]:
                    m1_current_idx = chord_progression_indices_base[i+1][0] + base_scale_len * 2

                bass_note_idx = chord_indices_voic_led[0] - (base_scale_len * 2)
                bass_events.append({'start_time': current_time, 'duration': chord_duration, 'freqs': [selected_scale_notes[max(0, bass_note_idx)]], 'volume': 0.6, 'articulation': 1.0, 'waveform': self.current_bass_waveform})
                
                chord_freqs = [selected_scale_notes[idx] for idx in chord_indices_voic_led]
                chord_events.append({'start_time': current_time, 'duration': chord_duration, 'freqs': chord_freqs, 'volume': 0.4, 'articulation': 1.0, 'waveform': self.current_chord_waveform})
                current_time += chord_duration
        else: 
            log_callback("  -> Generating energetic outro.", 'debug', debug_only=True)
            progression_romans = ['I', 'V', 'vi', 'IV', 'I'] if scale_type in self.MAJOR_LIKE_SCALES else ['i', 'v', 'VI', 'iv', 'i']
            key_root_note = selected_scale_name.split(' ')[0]
            chord_progression_indices_base = [self._get_chord_indices_from_roman(r, scale_type, key_root_note) for r in progression_romans]
            chord_duration = section_duration / len(chord_progression_indices_base) if chord_progression_indices_base else section_duration
            num_total_beats = int(round(section_duration / beat_duration))
            rhythm_phrases, _ = self._get_rhythm_sequence(num_total_beats, tension=0.6)
            
            m1_current_idx = (chord_progression_indices_base[0][0] if chord_progression_indices_base and chord_progression_indices_base[0] else 0) + base_scale_len * 2
            current_time, last_chord_indices_voic_led, chord_idx = 0.0, [], 0
            
            time_per_chord = section_duration / len(progression_romans) if progression_romans else section_duration
            
            for phrase in rhythm_phrases:
                for beat in phrase:
                    duration = abs(beat) * beat_duration
                    if current_time >= section_duration: break
                    
                    chord_idx = min(len(progression_romans)-1, int(current_time / time_per_chord))
                    current_chord_indices = chord_progression_indices_base[chord_idx]

                    if beat > 0:
                        m1_new_idx, _, _ = self._generate_melodic_note(m1_current_idx, m1_current_idx, selected_scale_notes, current_chord_indices, 0, 0, scale_type, log_callback, 'falling', 1.0)
                        melody1_events.append({'start_time': current_time, 'duration': duration, 'freqs': [selected_scale_notes[m1_new_idx]], 'scale_idx': [m1_new_idx], 'articulation': 1.0, 'volume': 0.6, 'waveform': self.current_m1_waveform})
                        m1_current_idx = m1_new_idx
                    
                    current_time += duration

            current_time = 0.0
            for i, chord_indices in enumerate(chord_progression_indices_base):
                if not chord_indices: continue
                chord_indices_voic_led = self._apply_voice_leading(last_chord_indices_voic_led, chord_indices, base_scale_len)
                last_chord_indices_voic_led = chord_indices_voic_led
                
                next_chord_indices = chord_progression_indices_base[i+1] if i + 1 < len(chord_progression_indices_base) else None

                bass_events.extend(self._generate_rhythmic_bass_events(current_time, chord_duration, chord_indices_voic_led, next_chord_indices, selected_scale_notes, base_scale_len, beat_duration, 0.6, self.current_bass_waveform, [], song_affect))
                chord_events.extend(self._generate_rhythmic_chord_events(current_time, chord_duration, chord_indices_voic_led, selected_scale_notes, base_scale_len, beat_duration, 0.6, self.current_chord_waveform, song_affect))
                current_time += chord_duration

        return {'melody1': melody1_events, 'melody2': [], 'bass': bass_events, 'chords': chord_events}

    def _apply_fade_out(self, audio, duration_s, sample_rate):
        self.update_log(f"Applying {duration_s}s fade out.", 'debug', debug_only=True)
        fade_samples = int(duration_s * sample_rate)
        if len(audio) > fade_samples:
            fade_curve = np.linspace(1.0, 0.0, fade_samples)[:, np.newaxis]
            audio[-fade_samples:] *= fade_curve
        return audio

    def _apply_reverb(self, audio, sample_rate, delay_sec=0.1, decay=0.4):
        self.update_log(f"Applying reverb effect.", 'debug', debug_only=True)
        delay_samples = int(delay_sec * sample_rate)
        reverb_buffer = np.zeros_like(audio)
        for i in range(delay_samples, len(audio)):
            reverb_buffer[i] = audio[i] + decay * reverb_buffer[i - delay_samples]
        return np.clip(reverb_buffer, -1.0, 1.0)


    def _apply_hybrid_envelope(self, audio_data, fade_duration_samples):
        total_samples = len(audio_data); fade_samples = min(fade_duration_samples, total_samples // 2)
        if fade_samples <= 1: return audio_data
        audio_data[:fade_samples] *= np.hanning(fade_samples * 2)[:fade_samples]
        audio_data[total_samples - fade_samples:] *= np.hanning(fade_samples * 2)[fade_samples:]
        return audio_data

    def _intelligently_select_waveforms(self, affect):
        self.update_log(f"Intelligently selecting waveforms for affect: {affect}", 'debug', debug_only=True)
        self.bass_waveform_var.set(random.choice(["Sine", "Square"]))
        self.chord_waveform_var.set(random.choice(["Cello", "Rich Saw"]))
        if affect == 'uplifting': m1_choice = random.choice(["Piano", "Violin", "Rich Saw", "Guitar"])
        elif affect == 'melancholy': m1_choice = random.choice(["Cello", "Hollow Square", "Piano", "Guitar"])
        elif affect == 'serene': m1_choice = random.choice(["Violin", "Sine", "Hollow Square", "Guitar"])
        elif affect == 'atonal': m1_choice = random.choice(["Vibraphone", "Glockenspiel", "Piano"])
        else: m1_choice = random.choice(["Rich Saw", "Violin", "Cello", "Guitar"])
        self.melody1_waveform_var.set(m1_choice)
        if m1_choice == "Piano": self.melody2_waveform_var.set(random.choice(["Sine", "Hollow Square", "Cello"]))
        elif m1_choice == "Rich Saw": self.melody2_waveform_var.set(random.choice(["Violin", "Sine"]))
        else: self.melody2_waveform_var.set("Sine")
        self.update_log("Auto-selected waveforms based on affect.", 'main')
        self.update_log(f"  -> M1: {self.melody1_waveform_var.get()}, M2: {self.melody2_waveform_var.get()}, Chords: {self.chord_waveform_var.get()}, Bass: {self.bass_waveform_var.get()}", 'debug', debug_only=True)

    def _create_melodic_lead_in(self, start_time, beat_duration, scale_notes, last_melody_event, next_section_first_chord_indices, base_scale_len):
        events = []
        if not last_melody_event or not next_section_first_chord_indices or not last_melody_event.get('scale_idx'):
            self.update_log("Skipping lead-in generation: missing required data.", 'debug', debug_only=True)
            return events

        last_note_idx = last_melody_event['scale_idx'][0]
        target_root_idx = next_section_first_chord_indices[0]
        
        octave_multiple = round((last_note_idx - target_root_idx) / base_scale_len)
        target_note_idx = max(0, min(len(scale_notes) - 1, target_root_idx + (octave_multiple * base_scale_len)))

        transition_style = random.choice(['crescendo_run', 'rhythmic_motif', 'harmonic_anticipation', 'melodic_fragment'])
        
        transition_start_time = start_time - (2 * beat_duration)
        self.update_log(f"Creating melodic lead-in ({transition_style}) from {transition_start_time:.2f}s to {start_time:.2f}s.", 'debug', debug_only=True)
        self.update_log(f"  Lead-in params: last_note_idx={last_note_idx}, target_root_idx={target_root_idx}, final_target_idx={target_note_idx}", 'debug', debug_only=True)

        if transition_style == 'crescendo_run':
            num_notes = 8
            direction = np.sign(target_note_idx - last_note_idx) or 1
            for i in range(num_notes):
                note_idx = last_note_idx + (i * direction)
                note_idx = max(0, min(len(scale_notes) - 1, note_idx))
                event = {
                    'start_time': transition_start_time + (i * beat_duration * 0.25),
                    'duration': beat_duration * 0.25, 'freqs': [scale_notes[note_idx]], 'scale_idx': [note_idx],
                    'volume': last_melody_event['volume'] * (0.8 + 0.2 * (i/num_notes)),
                    'waveform': last_melody_event['waveform']
                }
                events.append(event)

        elif transition_style == 'rhythmic_motif':
            rhythm = random.choice([[0.5, 0.5, 1.0], [0.25, 0.25, 0.5, 1.0]])
            current_rhythm_time = 0
            for dur in rhythm:
                event = {
                    'start_time': transition_start_time + current_rhythm_time,
                    'duration': dur * beat_duration, 'freqs': [scale_notes[target_note_idx]], 'scale_idx': [target_note_idx],
                    'volume': last_melody_event['volume'], 'waveform': last_melody_event['waveform']
                }
                events.append(event)
                current_rhythm_time += dur * beat_duration
                
        elif transition_style == 'harmonic_anticipation':
            arp_indices = []
            for chord_tone in next_section_first_chord_indices[:3]:
                 octave_mult = round((target_note_idx - chord_tone) / base_scale_len)
                 arp_indices.append(max(0, min(len(scale_notes) - 1, chord_tone + (octave_mult * base_scale_len))))
            
            for i, note_idx in enumerate(sorted(arp_indices)):
                event = {
                    'start_time': transition_start_time + (i * beat_duration * (2/3)),
                    'duration': beat_duration * (2/3), 'freqs': [scale_notes[note_idx]], 'scale_idx': [note_idx],
                    'volume': last_melody_event['volume'] * 0.9, 'waveform': last_melody_event['waveform']
                }
                events.append(event)
                
        elif transition_style == 'melodic_fragment':
            fragment_pattern = random.choice([[-2, -1, 0], [2, 1, 0], [-3, 1, 0]])
            for i, step in enumerate(fragment_pattern):
                note_idx = max(0, min(len(scale_notes) - 1, target_note_idx + step))
                event = {
                    'start_time': transition_start_time + (i * beat_duration * 0.5),
                    'duration': beat_duration * 0.5, 'freqs': [scale_notes[note_idx]], 'scale_idx': [note_idx],
                    'volume': last_melody_event['volume'], 'waveform': last_melody_event['waveform']
                }
                events.append(event)

        return events

    def _generate_full_song(self):
        log_callback = self.update_log
        log_callback("Starting full song generation...", 'debug', debug_only=True)
        total_duration = int(self.entry_duration.get()) if self.ui_mode else int(self.settings.get("duration", 90))
        self.last_bit_depth = int(self.bit_depth_var.get()) if self.ui_mode else int(self.settings.get("bit_depth", 24))
        self.last_sample_rate = 44100; self._generate_thematic_seed()
        
        song_affect = random.choice(['uplifting', 'melancholy', 'serene', 'intense', 'atonal'])
        if song_affect == 'uplifting': melody_bpm, affect_scale_choices = random.randint(120, 160), ["Major", "Pentatonic Major", "Lydian", "Mixolydian"]
        elif song_affect == 'melancholy': melody_bpm, affect_scale_choices = random.randint(70, 110), ["Minor", "Harmonic Minor", "Dorian"]
        elif song_affect == 'serene': melody_bpm, affect_scale_choices = random.randint(60, 90), ["Custom", "Pentatonic Major", "Lydian"]
        elif song_affect == 'atonal': melody_bpm, affect_scale_choices = random.randint(80, 120), ["Major"] # Use Major as a base for 12-tone mapping
        else: melody_bpm, affect_scale_choices = random.randint(130, 180), ["Phrygian Dominant", "Blues", "Melodic Minor", "Phrygian", "Locrian"]
        
        # Automatically set tension and dynamics based on song affect
        if song_affect in ['uplifting', 'intense']: global_tension, global_dynamics = random.uniform(0.6, 0.9), random.uniform(0.7, 1.0)
        elif song_affect in ['melancholy', 'serene']: global_tension, global_dynamics = random.uniform(0.1, 0.4), random.uniform(0.3, 0.6)
        elif song_affect == 'atonal': global_tension, global_dynamics = random.uniform(0.7, 1.0), random.uniform(0.2, 0.5)
        else: global_tension, global_dynamics = random.uniform(0.4, 0.7), random.uniform(0.5, 0.8)

        log_callback(f"Global Tension: {global_tension:.2f}, Global Dynamics: {global_dynamics:.2f}", 'main')
        
        melody_bpm += (global_tension - 0.5) * 40 
        
        beat_duration = 60.0 / melody_bpm
        self.last_melody_bpm = melody_bpm
        
        user_enabled_scales = [st for st, var in self.scale_vars.items() if var.get()]
        if not user_enabled_scales:
            self.update_log("No scales selected, choosing from all available scales.", 'main')
            user_enabled_scales = self.scale_types

        pitch_class_set = None
        if song_affect == 'atonal':
            pitch_class_set = random.choice(self.AFFECT_PITCH_SETS['atonal']['source_sets'])
            log_callback(f"Atonal Mode: Using Pitch-Class Set {pitch_class_set}", 'main')
            selected_scale_name = "C Major" # Base for chromatic mapping
        else:
            final_scale_choices = [s for s in user_enabled_scales if s in affect_scale_choices] or user_enabled_scales
            possible_scales = [name for name in self.MUSICAL_SCALES.keys() if name.split(' ', 1)[1] in final_scale_choices]
            selected_scale_name = random.choice(possible_scales) if possible_scales else "C Major"
        
        if self.ui_mode and self.auto_wave_var.get(): self._intelligently_select_waveforms(song_affect)
        
        texture_type = random.choices(['homophonic', 'polyphonic', 'heterophonic', 'counterpoint'], weights=[2, 2, 2, 2])[0]
        is_polyphonic, is_heterophonic = (texture_type == 'polyphonic'), (texture_type == 'heterophonic')
        is_polyrhythmic, is_polytonal = (texture_type != 'homophonic') and random.random() < 0.5, (texture_type != 'homophonic') and random.random() < 0.4
        log_callback(f"Generating {total_duration}s of music...", 'main')
        log_callback(f"Affect: {song_affect}, Texture: {texture_type.capitalize()}, Polyrhythmic: {is_polyrhythmic}, Polytonal: {is_polytonal}", 'main')
        self.current_m1_waveform, self.current_m2_waveform, self.current_chord_waveform, self.current_bass_waveform = self._get_waveform(self.melody1_waveform_var), self._get_waveform(self.melody2_waveform_var), self._get_waveform(self.chord_waveform_var), self._get_waveform(self.bass_waveform_var)
        
        user_enabled_forms = [ft for ft, var in self.form_vars.items() if var.get()]
        if not user_enabled_forms:
            self.update_log("No forms selected, choosing from all available forms.", 'main')
            user_enabled_forms = self.form_types
        song_form = random.choice(user_enabled_forms)

        drum_style = random.choice(list(self.DRUM_PATTERNS.keys()))
        log_callback(f"Key: {selected_scale_name}, Tempo: {melody_bpm:.0f} BPM, Form: {song_form}, Style: {drum_style}", 'main')
        
        SECTION_PROFILES = {
            'intro': {'m1_vol': 0.7, 'm2_vol': 0.0, 'bass_vol': 0.8, 'chords_vol': 0.6, 'drums': False},
            'verse': {'m1_vol': 0.9, 'm2_vol': 0.6, 'bass_vol': 0.9, 'chords_vol': 0.7, 'drums': True},
            'pre-chorus': {'m1_vol': 1.0, 'm2_vol': 0.7, 'bass_vol': 1.0, 'chords_vol': 0.8, 'drums': True},
            'chorus': {'m1_vol': 1.0, 'm2_vol': 0.8, 'bass_vol': 1.0, 'chords_vol': 0.9, 'drums': True},
            'bridge': {'m1_vol': 0.8, 'm2_vol': 0.0, 'bass_vol': 0.7, 'chords_vol': 1.0, 'drums': False},
            'solo': {'m1_vol': 1.0, 'm2_vol': 0.0, 'bass_vol': 1.0, 'chords_vol': 0.8, 'drums': True},
            'development': {'m1_vol': 0.9, 'm2_vol': 0.9, 'bass_vol': 0.9, 'chords_vol': 0.9, 'drums': True},
            'outro': {'m1_vol': 0.6, 'm2_vol': 0.0, 'bass_vol': 0.7, 'chords_vol': 0.8, 'drums': False}
        }
        SECTION_PROFILES['a'] = SECTION_PROFILES['verse']
        SECTION_PROFILES['b'] = SECTION_PROFILES['bridge']
        SECTION_PROFILES['c'] = SECTION_PROFILES['solo']
        SECTION_PROFILES['exposition_a'] = SECTION_PROFILES['verse']
        SECTION_PROFILES['exposition_b'] = SECTION_PROFILES['chorus']
        SECTION_PROFILES['recap_a'] = SECTION_PROFILES['verse']
        SECTION_PROFILES['recap_b'] = SECTION_PROFILES['chorus']

        structure, section_map = [], {}
        if song_form == "Theme and Variations": structure = ['verse'] + [f'verse_var_{i+1}' for i in range(4)]
        elif song_form == "Ternary": structure = ['A', 'B', 'A_reprise']
        elif song_form == "Rondo": structure = ['A', 'B', 'A_reprise', 'C', 'A_reprise']
        elif song_form == "AABA": structure = ['A', 'A_reprise', 'B', 'A_reprise']
        elif song_form == "Sonata":
            structure = ['Exposition_A', 'Exposition_B', 'Development', 'Recap_A', 'Recap_B']
            dominant_key = self._get_related_key(selected_scale_name, 'dominant')
            section_map = {'Exposition_A': {'prog': 'verse', 'key': selected_scale_name}, 'Exposition_B': {'prog': 'chorus', 'key': dominant_key}, 'Development': {'prog': 'development', 'key': selected_scale_name}, 'Recap_A': {'prog': 'verse', 'key': selected_scale_name}, 'Recap_B': {'prog': 'chorus', 'key': selected_scale_name}}
        else: structure = ['intro', 'verse', 'chorus', 'verse', 'chorus', 'bridge', 'chorus'] if total_duration > 60 else ['chorus', 'verse', 'chorus'] if total_duration >= 45 else ['chorus', 'verse']
        if total_duration > 60 and 'outro' not in structure: structure.append('outro')
        
        log_callback(f"Song Structure: {structure}", 'debug', debug_only=True)
        tension_map = {'intro':0.2, 'verse':0.4, 'pre-chorus':0.6, 'chorus':0.9, 'bridge':0.5, 'solo':1.0, 'development':0.8, 'outro':0.3, 'a':0.4, 'b':0.6, 'c':0.8, 'exposition_a':0.4, 'exposition_b':0.7, 'recap_a':0.5, 'recap_b':0.8}
        
        schenker_urlinie = self._generate_urlinie(len(structure), len(self.MUSICAL_SCALES[selected_scale_name]))

        section_data_cache, section_duration = {}, total_duration / len(structure)
        full_song_data, full_drum_data, current_time, section_log_timeline = {'melody1': [], 'melody2': [], 'bass': [], 'chords': []}, [], 0.0, []
        
        for i, section_name in enumerate(structure):
            progression_name = section_name.split('_')[0].lower()
            if progression_name == 'a': progression_name = 'verse'
            elif progression_name == 'b': progression_name = 'bridge'
            elif progression_name == 'c': progression_name = 'solo'
            elif progression_name.startswith(('exposition', 'recap')): progression_name = section_map[section_name]['prog']
            
            base_tension = tension_map.get(progression_name, 0.5)
            section_tension = base_tension + (global_tension - 0.5) * 0.5 
            
            log_callback(f"--- Generating {section_name.title()} (as {progression_name}) ---", 'main')
            section_log_timeline.append({'start_time': current_time, 'log_type': 'main', 'message': f"--- Playing {section_name.title()} ---"})
            original_section_name = section_name.split('_')[0]
            
            section_profile = SECTION_PROFILES.get(progression_name, SECTION_PROFILES['verse'])

            section_data = None
            current_key = section_map.get(section_name, {}).get('key', selected_scale_name)
            current_scale_notes_base = self.MUSICAL_SCALES[current_key]
            current_scale_notes = [f/2 for f in current_scale_notes_base] + current_scale_notes_base + [f*2 for f in current_scale_notes_base] + [f*4 for f in current_scale_notes_base]
            if current_key != selected_scale_name: log_callback(f"Modulating to key: {current_key}", 'main')

            urlinie_segment = [schenker_urlinie[i]] * len(self.CHORD_PROGRESSIONS.get(current_key.split(' ')[1], {}).get(progression_name, [1,1,1,1]))

            if 'outro' in section_name:
                section_data = self._generate_outro_section_data(current_key, current_scale_notes, current_key.split(' ', 1)[1], section_duration, melody_bpm, log_callback, current_scale_notes_base, song_affect)
                drum_data = []
            elif '_reprise' in section_name and original_section_name in section_data_cache:
                log_callback(f"Using cached data for reprise of '{original_section_name}'", 'debug', debug_only=True)
                section_data, drum_data = copy.deepcopy(section_data_cache[original_section_name]['section']), copy.deepcopy(section_data_cache[original_section_name]['drums'])
            else:
                section_data = self._generate_song_section_data(current_key, current_scale_notes, current_key.split(' ', 1)[1], progression_name, section_duration, melody_bpm, log_callback, current_scale_notes_base, texture_type, song_affect, tension=section_tension, is_heterophonic=is_heterophonic, is_reprise=('_reprise' in section_name), is_polyrhythmic=is_polyrhythmic, is_polytonal=is_polytonal, section_profile=section_profile, urlinie_segment=urlinie_segment, pitch_class_set=pitch_class_set)
                
                if section_profile.get('drums', True) and song_affect != 'atonal':
                    drum_data = self._generate_dynamic_drum_rhythm(progression_name, section_duration, melody_bpm, drum_style, section_tension)
                else:
                    drum_data = []

                if original_section_name in ['A', 'B', 'C', 'chorus', 'verse']: 
                    log_callback(f"Caching data for section '{original_section_name}'", 'debug', debug_only=True)
                    section_data_cache[original_section_name] = {'section': section_data, 'drums': drum_data}
            
            # --- Humanization and Dynamic Contouring ---
            for part in ['melody1', 'melody2', 'bass', 'chords']:
                section_data[part] = self._apply_dynamic_contouring(section_data[part], global_dynamics)
                section_data[part] = self._humanize_part(section_data[part], global_dynamics)

            for part, events in section_data.items():
                for item in events: 
                    item_copy = item.copy()
                    item_copy['start_time'] += current_time
                    full_song_data[part].append(item_copy)

            for item in drum_data: 
                item_copy = item.copy()
                item_copy['start_time'] += current_time
                full_drum_data.append(item_copy)
                
            if i < len(structure) - 1:
                transition_type = random.choice(['lead_in', 'drum_break', 'pause'])
                log_callback(f"Transition choice: {transition_type}", 'debug', debug_only=True)
                
                transition_duration_beats = 2
                transition_duration_sec = transition_duration_beats * beat_duration
                transition_start_time = current_time + section_duration - transition_duration_sec
                log_callback(f"  Transition window: {transition_start_time:.2f}s to {current_time + section_duration:.2f}s", 'debug', debug_only=True)

                for part in ['melody1', 'melody2', 'bass', 'chords']:
                    for event in full_song_data[part]:
                        if event['start_time'] >= current_time:
                            event_end_time = event['start_time'] + event['duration']
                            if event_end_time > transition_start_time:
                                original_duration = event['duration']
                                new_duration = transition_start_time - event['start_time']
                                event['duration'] = max(0.01, new_duration)
                                log_callback(f"  Trimming event of '{part}' from {original_duration:.2f}s to {event['duration']:.2f}s to make room.", 'debug', debug_only=True)

                if transition_type == 'lead_in' and full_song_data['melody1']:
                    last_melody_event = max(full_song_data['melody1'], key=lambda x: x['start_time'])
                    
                    next_section_name = structure[i+1]
                    next_progression_name = next_section_name.split('_')[0].lower()
                    
                    prog_map = {'a': 'verse', 'b': 'bridge', 'c': 'solo'}
                    if next_progression_name in prog_map: next_progression_name = prog_map[next_progression_name]
                    elif next_progression_name.startswith(('exposition', 'recap')): next_progression_name = section_map[next_section_name]['prog']

                    next_key = section_map.get(next_section_name, {}).get('key', selected_scale_name)
                    next_scale_type = next_key.split(' ', 1)[1]
                    next_scale_notes_base = self.MUSICAL_SCALES[next_key]
                    next_scale_notes = [f/2 for f in next_scale_notes_base] + next_scale_notes_base + [f*2 for f in next_scale_notes_base] + [f*4 for f in next_scale_notes_base]
                    
                    next_progression_romans = self.CHORD_PROGRESSIONS.get(next_scale_type, {}).get(next_progression_name, [])
                    next_first_chord_indices = self.DIATONIC_CHORDS[next_scale_type].get(next_progression_romans[0], []) if next_progression_romans else []
                    
                    lead_in_events = self._create_melodic_lead_in(
                        start_time=(current_time + section_duration),
                        beat_duration=beat_duration, scale_notes=next_scale_notes,
                        last_melody_event=last_melody_event, next_section_first_chord_indices=next_first_chord_indices,
                        base_scale_len=len(next_scale_notes_base)
                    )
                    full_song_data['melody1'].extend(lead_in_events)

                elif transition_type == 'drum_break':
                    fill_start_time = current_time + section_duration - (2 * beat_duration)
                    log_callback(f"Creating 2-beat drum break starting at {fill_start_time:.2f}s.", 'debug', debug_only=True)
                    for beat in range(8):
                        if random.random() < 0.7:
                            drum_type = random.choice(['snare', 'snare', 'tom'])
                            hit_time = fill_start_time + (beat * beat_duration * 0.25)
                            full_drum_data.append({'start_time': hit_time, 'duration': beat_duration * 0.25, 'drum_type': drum_type, 'volume': 0.8 + (beat/16)})
                    full_drum_data.append({'start_time': current_time + section_duration, 'duration': beat_duration, 'drum_type': 'crash', 'volume': 1.0})
                
                else:
                    log_callback(f"Creating 2-beat pause transition.", 'debug', debug_only=True)

            current_time += section_duration

        self.update_log("Finished generating all song data.", 'debug', debug_only=True)
        return full_song_data, full_drum_data, section_log_timeline, 'fade_out', current_time, melody_bpm
    
    def _normalize_segment(self, segment, target_rms=0.1):
        if segment.size == 0:
            return segment
        
        current_rms = np.sqrt(np.mean(segment**2))
        if current_rms < 1e-6: 
            return segment
        
        gain = target_rms / current_rms
        normalized_segment = segment * gain
        
        peak = np.max(np.abs(normalized_segment))
        if peak > 0.99:
            normalized_segment /= peak
            
        return normalized_segment

    def _music_generation_and_playback_thread(self, initial_melody_volume, initial_harmony_volume, initial_drum_volume, on_finish_callback):
        try:
            full_song_data, full_drum_data, section_log_timeline, ending_style, total_duration, melody_bpm = self._generate_full_song()
            
            self.last_song_data = full_song_data
            self.last_drum_data = full_drum_data
            self.last_melody_bpm = melody_bpm

            SAMPLE_RATE = self.last_sample_rate
            total_samples = int(total_duration * SAMPLE_RATE) + int(SAMPLE_RATE * 5)
            self.update_log(f"Allocating audio buffers for {total_duration:.2f}s ({total_samples} samples)", 'debug', debug_only=True)
            
            # --- SOUNDBOARD SIMULATION ---
            # A simple convolution with an impulse response can simulate a soundboard.
            # For simplicity, we create a basic decaying noise impulse response.
            ir_length = int(SAMPLE_RATE * 1.5)
            soundboard_ir = (np.random.rand(ir_length, 2) - 0.5) * 0.1
            soundboard_ir *= np.linspace(1, 0, ir_length)[:, np.newaxis]**2
            
            part_tracks = {part: np.zeros((total_samples, 2), dtype=np.float64) for part in full_song_data.keys()}
            drum_track = np.zeros((total_samples, 2), dtype=np.float64)
            fade_samples = int(0.005 * SAMPLE_RATE)
            
            pan_values = {
                'melody1': self.m1_pan_slider.get() / 100.0 if self.ui_mode else -0.2,
                'melody2': self.m2_pan_slider.get() / 100.0 if self.ui_mode else 0.2,
                'bass': self.bass_pan_slider.get() / 100.0 if self.ui_mode else 0.0,
                'chords': self.chord_pan_slider.get() / 100.0 if self.ui_mode else 0.0,
            }
            
            for part_name, events in full_song_data.items():
                self.update_log(f"Rendering audio for part: {part_name}", 'debug', debug_only=True)
                track = part_tracks[part_name]
                for item in events:
                    effective_duration = item['duration']
                    if item['waveform'] in self.RESONANT_WAVEFORMS and item['duration'] < self.MIN_RESONANT_DURATION:
                        effective_duration = self.MIN_RESONANT_DURATION
                    
                    raw_segment = self._generate_tone(effective_duration, SAMPLE_RATE, item['freqs'], item['waveform'])
                    if raw_segment.size == 0: continue
                    normalized_segment = self._normalize_segment(raw_segment)
                    amplitude_factor = 1.0; ref_freq = 440.0
                    if item['waveform'] in ['Square', 'Sawtooth', 'Triangle', 'Rich Saw', 'Violin', 'Guitar']:
                        rolloff_exponent = 0.3; frequency = item['freqs'][0] if item['freqs'] else ref_freq
                        amplitude_factor = (ref_freq / max(ref_freq, frequency)) ** rolloff_exponent

                    final_segment = self._apply_hybrid_envelope(normalized_segment * amplitude_factor, fade_samples)

                    pan = pan_values.get(part_name, 0.0)
                    left_gain = math.sqrt(0.5 * (1 - pan))
                    right_gain = math.sqrt(0.5 * (1 + pan))
                    stereo_segment = np.column_stack((final_segment * left_gain, final_segment * right_gain))

                    start_s, end_s = int(item['start_time'] * SAMPLE_RATE), int(item['start_time'] * SAMPLE_RATE) + len(stereo_segment)
                    if start_s < 0 or end_s > total_samples: continue
                    track[start_s:end_s] += stereo_segment * item.get('volume', 0.7)
            
            self.update_log("Rendering audio for drums", 'debug', debug_only=True)
            for item in full_drum_data:
                raw_segment = self._generate_percussion_sound(item['drum_type'], item['duration'], SAMPLE_RATE)
                if raw_segment.size == 0: continue
                normalized_segment = self._normalize_segment(raw_segment, target_rms=0.15)
                
                stereo_segment = np.column_stack((normalized_segment, normalized_segment))

                start_s, end_s = int(item['start_time'] * SAMPLE_RATE), int(item['start_time'] * SAMPLE_RATE) + len(stereo_segment)
                if start_s < 0 or end_s > total_samples: continue
                if drum_track[start_s:end_s].shape == stereo_segment.shape: drum_track[start_s:end_s] += stereo_segment * item.get('volume', 1.0)
                else: self.update_log(f"Debug: Shape mismatch. Slice: {drum_track[start_s:end_s].shape}, Segment: {stereo_segment.shape}", 'debug', debug_only=True)
            
            self.update_log("Mixing audio tracks...", 'debug', debug_only=True)
            melody_track = part_tracks['melody1'] + part_tracks['melody2']
            harmony_track = part_tracks['bass'] + part_tracks['chords']
            
            # --- Mixdown and Master Effects ---
            master_pre_effects = (melody_track * initial_melody_volume) + \
                                 (harmony_track * initial_harmony_volume) + \
                                 (drum_track * initial_drum_volume)

            # Apply soundboard convolution
            master_with_soundboard = signal.convolve(master_pre_effects, soundboard_ir, mode='same')
            
            master_with_reverb = self._apply_reverb(master_with_soundboard, SAMPLE_RATE)

            if ending_style == 'fade_out': master_with_reverb = self._apply_fade_out(master_with_reverb, 4.0, SAMPLE_RATE)
            master_audio = np.tanh(master_with_reverb * 1.2) # Soft clipping/limiter
            self.last_master_audio = master_audio
            
            self.update_log("Preparing audio for playback...", 'debug', debug_only=True)
            
            def to_pygame_sound(stereo_track): 
                clipped_track = np.clip(stereo_track, -1.0, 1.0)
                int_track = (clipped_track * 32767.0).astype(np.int16)
                return pygame.sndarray.make_sound(int_track)

            self.last_melody_sound = to_pygame_sound(melody_track)
            self.last_harmony_sound = to_pygame_sound(harmony_track)
            self.last_drum_sound = to_pygame_sound(drum_track)

            self.melody_channel = pygame.mixer.Channel(0); self.harmony_channel = pygame.mixer.Channel(1); self.drum_channel = pygame.mixer.Channel(2)
            self.update_melody_volume(self.melody_volume_slider.get()); self.update_harmony_volume(self.harmony_volume_slider.get()); self.update_drum_volume(self.drum_volume_slider.get())
            
            self.melody_channel.play(self.last_melody_sound); self.harmony_channel.play(self.last_harmony_sound); self.drum_channel.play(self.last_drum_sound)
            
            log_timeline = []
            log_map = {'melody1': 'melody1', 'melody2': 'melody2', 'bass': 'bass', 'chords': 'chords'}
            for part, events in full_song_data.items():
                log_type = log_map.get(part)
                if not events or not log_type: continue
                for item in events:
                    notes_str = ', '.join(self._find_closest_note_name(f) for f in item['freqs'])
                    log_timeline.append({'start_time': item['start_time'], 'log_type': log_type, 'message': f"Time: {item['start_time']:.2f}s | {notes_str} ({item['waveform']})"})
            
            for item in full_drum_data: 
                log_timeline.append({'start_time': item['start_time'], 'log_type': 'drums', 'message': f"Time: {item['start_time']:.2f}s | Drum: {item['drum_type']}"})

            log_timeline.extend(section_log_timeline)
            log_timeline.sort(key=lambda x: x['start_time'])
            
            self.update_log("--- Starting Playback ---", 'main')
            start_playback_time, log_index = time.time(), 0
            
            while (self.melody_channel.get_busy() or self.harmony_channel.get_busy() or self.drum_channel.get_busy()) and not self.stop_event.is_set():
                elapsed_time = time.time() - start_playback_time
                while log_index < len(log_timeline) and elapsed_time >= log_timeline[log_index]['start_time']:
                    entry = log_timeline[log_index]; self.update_log(entry['message'], entry['log_type']); log_index += 1
                time.sleep(0.01)
            self.update_log("--- Playback Finished ---", 'main')

        except Exception: 
            self.update_log(f"An unexpected error occurred:\n{traceback.format_exc()}", 'main')
            self.update_log(f"Full traceback:\n{traceback.format_exc()}", 'debug', debug_only=True)
        finally:
            if self.melody_channel: self.melody_channel.stop()
            if self.harmony_channel: self.harmony_channel.stop()
            if self.drum_channel: self.drum_channel.stop()
            if self.ui_mode: self.master.after(0, on_finish_callback)

    def run_headless(self, loop=False):
        print("Headless mode started. Using settings from harmonizer_settings.json")
        try:
            pygame.mixer.init(frequency=44100, size=-16, channels=2, buffer=1024)
            while True:
                full_song_data, full_drum_data, section_log_timeline, ending_style, total_duration, melody_bpm = self._generate_full_song()
                print("\n--- SONG GENERATION FINISHED, NOT IMPLEMENTED FOR HEADLESS PLAYBACK YET ---\n")
                if not loop: break
                time.sleep(2)
        except KeyboardInterrupt: print("\nExiting.")
        finally: pygame.mixer.quit()

    def on_closing(self): self._save_settings(); self.stop_event.set(); pygame.mixer.quit(); self.master.destroy() if self.ui_mode else None
    def on_playback_finished(self):
        if self.lock.locked(): self.lock.release()
        self.generation_complete = True
        self._safe_reset_ui()
    def update_log(self, text, log_type='main', debug_only=False):
        if not self.ui_mode: print(f"[{'DEBUG' if debug_only else log_type.upper()}] {text}"); return
        if self.debug_window and self.debug_window.winfo_exists():
            self.debug_log_area.configure(state='normal'); self.debug_log_area.insert(tk.END, f"[{log_type.upper()}] {text}\n"); self.debug_log_area.configure(state='disabled'); self.debug_log_area.see(tk.END)
        if debug_only: return
        widget = {'main': self.main_log_area, 'melody1': self.melody1_log_area, 'melody2': self.melody2_log_area, 'bass': self.bass_log_area, 'chords': self.chord_log_area, 'drums': self.drum_log_area}.get(log_type)
        if widget: widget.configure(state='normal'); widget.insert(tk.END, text + "\n", log_type); widget.configure(state='disabled'); widget.see(tk.END)
    def _safe_reset_ui(self):
        self.play_button.config(state=tk.NORMAL); self.replay_button.config(state=tk.NORMAL if self.last_drum_sound is not None else tk.DISABLED)
        self.stop_button.config(state=tk.DISABLED)
        self.export_wav_button.config(state=tk.NORMAL if self.last_master_audio is not None else tk.DISABLED)
        self.export_midi_button.config(state=tk.NORMAL if self.last_song_data is not None else tk.DISABLED)
        if self.loop_var.get() and not self.stop_event.is_set(): self.master.after(100, self.start_music)
    def _update_and_save_melody_volume(self, vol): self.update_melody_volume(vol); self._save_settings()
    def _update_and_save_harmony_volume(self, vol): self.update_harmony_volume(vol); self._save_settings()
    def _update_and_save_drum_volume(self, vol): self.update_drum_volume(vol); self._save_settings()
    def update_melody_volume(self, vol):
        if self.melody_channel: self.melody_channel.set_volume(float(vol) / 100.0)
    def update_harmony_volume(self, vol):
        if self.harmony_channel: self.harmony_channel.set_volume(float(vol) / 100.0)
    def update_drum_volume(self, vol):
        if self.drum_channel: self.drum_channel.set_volume(float(vol) / 100.0)
    def start_music(self):
        if not self.lock.acquire(blocking=False): self.update_log("Generation already in progress.", 'main'); return
        self.generation_complete = False
        self.last_song_data = None
        self.last_drum_data = None
        self.play_button.config(state=tk.DISABLED); self.replay_button.config(state=tk.DISABLED); self.stop_button.config(state=tk.NORMAL)
        self.export_wav_button.config(state=tk.DISABLED); self.export_midi_button.config(state=tk.DISABLED); self.stop_event.clear()
        for log in [self.main_log_area, self.melody1_log_area, self.melody2_log_area, self.bass_log_area, self.chord_log_area, self.drum_log_area]: log.configure(state='normal'); log.delete('1.0', tk.END); log.configure(state='disabled')
        if self.debug_log_area: self.debug_log_area.configure(state='normal'); self.debug_log_area.delete('1.0', tk.END); self.debug_log_area.configure(state='disabled')
        self.last_melody_sound, self.last_harmony_sound, self.last_drum_sound = None, None, None
        initial_melody_volume = self.melody_volume_slider.get() / 100.0
        initial_harmony_volume = self.harmony_volume_slider.get() / 100.0
        initial_drum_volume = self.drum_volume_slider.get() / 100.0
        self.music_thread = threading.Thread(target=self._music_generation_and_playback_thread, args=(initial_melody_volume, initial_harmony_volume, initial_drum_volume, self.on_playback_finished)); self.music_thread.start()
    def replay_music(self):
        if self.last_drum_sound is None: self.update_log("No song generated yet.", 'main'); return
        if not self.lock.acquire(blocking=False): self.update_log("Playback already in progress.", 'main'); return
        self.play_button.config(state=tk.DISABLED); self.replay_button.config(state=tk.DISABLED); self.stop_button.config(state=tk.NORMAL); self.stop_event.clear()
        def playback_thread_target(on_finish_callback):
            try:
                self.melody_channel, self.harmony_channel, self.drum_channel = pygame.mixer.Channel(0), pygame.mixer.Channel(1), pygame.mixer.Channel(2)
                self.update_melody_volume(self.melody_volume_slider.get())
                self.update_harmony_volume(self.harmony_volume_slider.get())
                self.update_drum_volume(self.drum_volume_slider.get())
                self.melody_channel.play(self.last_melody_sound)
                self.harmony_channel.play(self.last_harmony_sound)
                self.drum_channel.play(self.last_drum_sound)
                while (self.melody_channel.get_busy() or self.harmony_channel.get_busy() or self.drum_channel.get_busy()) and not self.stop_event.is_set(): time.sleep(0.01)
                self.update_log("Replay Finished.", 'main')
            except Exception as e: self.update_log(f"Error during replay: {e}", 'main')
            finally:
                if self.melody_channel: self.melody_channel.stop()
                if self.harmony_channel: self.harmony_channel.stop()
                if self.drum_channel: self.drum_channel.stop()
                self.master.after(0, on_finish_callback)
        self.music_thread = threading.Thread(target=playback_thread_target, args=(self.on_playback_finished,)); self.music_thread.start()
    def stop_music(self): self.update_log("Stop pressed.", "debug", debug_only=True); self.stop_event.set()
    def export_wav_file(self):
        if not self.generation_complete or self.last_master_audio is None: self.update_log("No audio to export.", 'main'); return
        filename = filedialog.asksaveasfilename(defaultextension=".wav", filetypes=[("WAV files", "*.wav")])
        if not filename: return
        audio_to_save = np.clip(self.last_master_audio, -1.0, 1.0)
        with wave.open(filename, 'wb') as f:
            f.setnchannels(2); f.setsampwidth(self.last_bit_depth // 8); f.setframerate(self.last_sample_rate)
            if self.last_bit_depth == 24:
                audio_data_int = (audio_to_save * (2**23 - 1)).astype(np.int32)
                byte_data = bytearray()
                for l_sample, r_sample in audio_data_int:
                    byte_data.extend(l_sample.to_bytes(4, byteorder='little', signed=True)[:3])
                    byte_data.extend(r_sample.to_bytes(4, byteorder='little', signed=True)[:3])
                f.writeframes(bytes(byte_data))
            else:
                audio_data_int16 = (audio_to_save * 32767.0).astype(np.int16)
                f.writeframes(audio_data_int16.tobytes())
        self.update_log(f"Exported to {filename}", 'main')
    
    def export_midi_file(self):
        if not self.generation_complete or not self.last_song_data:
            self.update_log("No song data to export. Please generate a song first.", 'main')
            return
        has_musical_data = any(events for events in self.last_song_data.values())
        if not self.last_drum_data and not has_musical_data:
            self.update_log("Generated song has no musical data to export.", 'main')
            return
        filename = filedialog.asksaveasfilename(defaultextension=".mid", filetypes=[("MIDI files", "*.mid")])
        if not filename: return
        try:
            def freq_to_midi(f):
                if f <= 0: return 0
                return 69 + 12 * math.log2(f / 440.0)

            midi = MIDIFile(10, deinterleave=False)
            beat_dur = 60.0 / self.last_melody_bpm
            midi.addTempo(0, 0, self.last_melody_bpm)

            track_map = {
                'melody1': {'track': 1, 'channel': 0, 'program': self.MIDI_INSTRUMENTS[self.midi_m1_var.get()]},
                'melody2': {'track': 2, 'channel': 1, 'program': self.MIDI_INSTRUMENTS[self.midi_m2_var.get()]},
                'bass':    {'track': 3, 'channel': 2, 'program': self.MIDI_INSTRUMENTS[self.midi_bass_var.get()]},
                'chords':  {'track': 4, 'channel': 3, 'program': self.MIDI_INSTRUMENTS[self.midi_chord_var.get()]},
            }

            for part, config in track_map.items():
                midi.addProgramChange(config['track'], config['channel'], 0, config['program'])

            for part, config in track_map.items():
                if part in self.last_song_data:
                    for item in self.last_song_data[part]:
                        start_beat = item['start_time'] / beat_dur
                        dur_beats = item['duration'] / beat_dur
                        if dur_beats <= 0: continue
                        
                        volume = int(item.get('volume', 0.7) * 127)
                        for freq in item['freqs']:
                            midi_note = int(round(freq_to_midi(freq)))
                            if 0 < midi_note < 128:
                                midi.addNote(config['track'], config['channel'], midi_note, start_beat, dur_beats, volume)
            if self.last_drum_data:
                drum_track = 9; drum_channel = 9
                for item in self.last_drum_data:
                    start_beat = item['start_time'] / beat_dur
                    dur_beats = item['duration'] / beat_dur
                    if dur_beats <= 0: continue
                    volume = int(item.get('volume', 0.8) * 127)
                    midi_note = self.DRUM_SOUND_PROPERTIES[item['drum_type']]['midi_note']
                    if 0 < midi_note < 128:
                        midi.addNote(drum_track, drum_channel, midi_note, start_beat, dur_beats, volume)
            with open(filename, "wb") as f:
                midi.writeFile(f)
            self.update_log(f"Exported MIDI to {filename}", 'main')
        except Exception as e:
            self.update_log(f"Error exporting MIDI: {e}", 'main')
            self.update_log(traceback.format_exc(), 'debug', debug_only=True)

    def reload_script(self): self.stop_music(); pygame.mixer.quit(); self.master.destroy(); os.execl(sys.executable, sys.executable, *sys.argv)

if __name__ == "__main__":
    if '--no-ui' in sys.argv:
        app = HarmonizerApp(master=None, ui_mode=False)
        app.run_headless(loop='--loop' in sys.argv)
    else:
        root = tk.Tk()
        app = HarmonizerApp(root)
        root.mainloop()



