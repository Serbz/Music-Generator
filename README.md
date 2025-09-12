Tones Generator & Harmonizer

A powerful Python script that composes original, complex music on the fly using a deep foundation of music theory.

Overview
The Tones Generator & Harmonizer is a powerful Python script that composes original music on the fly. It's built on a deep foundation of music theory, allowing it to create complex and stylistically rich pieces right before your ears. It comes with a user-friendly interface (made with Tkinter) that gives you real-time control over the music generation process.
From simple melodies to full-band arrangements with multiple harmonies, basslines, and drum beats, this tool does it all by synthesizing every sound from scratch. For more automated tasks, you can even run it without the interface from your command line.
Key Features


Compose Full Songs: Generate multi-part arrangements with two melody lines, chords, bass, and drums, all working together.
A Deep Musical Brain: This isn't just random notes. The generator understands and uses a huge library of music theory:
Scales & Modes: Go beyond Major and Minor with over a dozen scales, including Lydian, Blues, Pentatonics, and more.
Smart Harmony: Creates believable chord progressions using concepts like diatonic chords, modal interchange, secondary dominants, and proper voice leading.
Creative Melodies: Melodies are crafted with sophisticated techniques like Schenkerian analysis, L-Systems, and species counterpoint to feel intentional and structured.
Real Song Structures: Build music in classic forms like Sonata, Rondo, A-B-A, and the familiar verse-chorus structure.



Built-in Synthesizer:
All sounds are generated from scratch—no samples required!
Create classic synth sounds with Sine, Square, Sawtooth, and Triangle waves.
Features surprisingly realistic synthesized instruments like Piano, Violin, Cello, and Guitar.
Even the drum kit (kick, snare, hi-hats) is synthesized in real-time.





Hands-On Control:
A simple interface lets you direct the creation process.
Control playback, adjust the song's length, tempo, and overall energy.
Mix the volume and stereo pan of each instrument section.
Choose exactly which scales and song structures you want the generator to use.





Export:
Save your song as a high-quality stereo WAV file (16 or 24-bit).
Export a MIDI file to drop into your favorite DAW (like Ableton, FL Studio, or Logic) and use with your own virtual instruments.
Easy Setup: The script automatically finds and installs the libraries it needs to run.






Dependencies
The script will try to install these for you. If it runs into trouble, you can install them yourself with pip:

pygame
scipy
midiutil
matplotlib
numpy





How to Use

Save the script: Save the code as TonesGenerator.py.
Run it: Open a terminal or command prompt, cd into the folder where you saved the file, and run it:
python TonesGenerator.py
The GUI will appear. Use the controls to start making music!

Command-Line Options

Headless Mode: Run without the GUI. It will generate one song based on your last saved settings and then exit.
python TonesGenerator.py --no-ui
Headless Loop Mode: Run without the GUI and continuously generate new songs until you stop it (Ctrl+C).
python TonesGenerator.py --no-ui --loop






GUI Controls Explained

Play: Generates and plays a new song with your current settings.
Replay: Plays back the last song you generated.
Stop: Halts whatever is currently playing or generating.
Loop: When checked, a new song will start as soon as the current one finishes.
Duration (s): Sets the approximate length for the generated song in seconds.
Scales: Opens a window where you can pick which musical scales the generator is allowed to use.
Form: Lets you choose the song structures you want to hear (e.g., Sonata, Rondo). The generator will randomly select from your enabled choices.
Waveforms
Auto-Select: If you check this, the app will intelligently pick instrument sounds based on the mood of the generated song.
Melody 1/2, Chords, Bass Dropdowns: Manually pick the sound for each part of the band.

Mixer & Generation
Volume Sliders: Your mixing board for the main instrument groups.
Tension: This is the "energy" knob. Cranking it up leads to faster tempos, more complex rhythms, and fancier melodic runs. Dial it back for something more relaxed.
Dynamics: Controls how much the volume swells and fades within phrases, making the performance sound more human and expressive.
Pan Sliders: Place each instrument in the stereo field (left, right, or center).

Export & MIDI
MIDI Instrument Menus: Assigns a standard MIDI instrument to each part for when you export a MIDI file. This doesn't change the sound you hear in the app itself.
Export WAV: Saves the final audio as a stereo WAV file.
Bit Depth: Choose between 16-bit and 24-bit quality for your WAV export.
Export MIDI: Saves the song's "sheet music" as a MIDI file that you can edit in other music software.
Reload: Restarts the script. A good first step if things get stuck.
