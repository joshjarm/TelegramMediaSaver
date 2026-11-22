# Telegram Media Saver Fast

A desktop app for bulk-downloading media from your Telegram chats, channels and groups, sorted into
folders by type: Photos, Videos, Voice messages, Video messages, Stickers, GIFs and Files.

Built for big jobs: files that are already downloaded are never fetched again, interrupted downloads
resume, and a summary at the end lists anything that didn't make it.

## Features

- **Two download engines**
  - **Built-in** (`tg_engine.py`), based on Telethon. It splits every file across several
    connections and fetches message details 100 at a time.
  - **[tdl](https://github.com/iyear/tdl)**, if you already use it. Supports Telegram's "takeout"
    export mode.
- **Pick what to save:** choose chats, forum topics (include/exclude filters) and media types.
- **Skips duplicates:** point it at one or more reference folders, even on other drives, and
  anything already there is skipped. A duplicate finder and download verifier are included.
- **Live view:** every file in progress with speed and ETA. Colours show its state: green = done,
  orange = Telegram is making us wait, red = failed and retried on the next Start.
- **Speed graph:** speed (MB/s) and amount downloaded over time. Choose from 11 styles, 13 time
  ranges plus a custom one, adjustable update rate and colour themes.
- **Safe for long runs:** pause, stop, save progress and resume later. Disk space is checked
  before starting and the PC is kept awake while downloading.
- **Dockable layout:** drag, resize, hide and restore sections, and save named layouts.
- **Themes and settings:** many dark and QD-OLED colour themes plus your own custom themes. The
  Settings window covers fonts, scale, density, animations, glow, sounds and more.

## Requirements

- Windows 10/11 (the GUI also starts on Linux, but it is developed and tested on Windows)
- Python 3.9 or newer, with tkinter (included in the python.org installer)
- For the Built-in engine:

  ```
  py -m pip install telethon cryptg
  ```

  `cryptg` makes decryption fast. Without it, downloads fall back to slower methods.
- A Telegram API ID and hash. Get your own free at <https://my.telegram.org/apps>.
- Optional: [tdl](https://github.com/iyear/tdl), only if you want to use it as the engine.

## Getting started

1. Download `tmsf.py` and `tg_engine.py` from the
   [latest release](../../releases/latest) and keep them in the same folder.
2. Run:

   ```
   py tmsf.py
   ```

3. Choose **Engine: Built-in**. On first use, sign in with your API ID/hash, phone number,
   login code and 2FA password if you have one.
4. Pick a save folder, the chats and the media types, then press **Start**.

### Command-line options

| Option | Description |
| --- | --- |
| `-d`, `--dir PATH` | Folder where new downloads are saved |
| `-r`, `--ref-dir PATHS` | Reference folder(s) to check for files already downloaded, separated by `;` |

## Where your data is stored

Your Telegram login (session), API keys and app settings are stored on your own PC only, never in
this repository:

- Windows: `%APPDATA%\TelegramMediaSaver`
- Linux: `~/.config/TelegramMediaSaver`

Don't share that folder: the session file gives access to your Telegram account.

## Limitations

- Pictures and videos inside link previews are not downloaded.
- Telegram's export doesn't label GIFs directly. They are recognised as MP4 files with the
  "animated" marker, so very rarely a normal video can be counted as a GIF.
- Telegram limits how fast accounts can fetch data. When it asks the app to wait (FloodWait),
  the app waits and continues automatically.
