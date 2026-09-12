import os, io, re, math, random, asyncio, subprocess, tempfile, shutil, textwrap, time, logging
from pathlib import Path
from PIL import Image, ImageOps, ImageEnhance, ImageFilter, ImageDraw, ImageFont
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import ContextTypes

BASE_DIR = Path(os.getenv('RANDOMUNDERGROUND_DATA_DIR', '.')).resolve()
UPLOAD_DIR = BASE_DIR / 'creative_uploads'
RENDER_DIR = BASE_DIR / 'creative_renders'
TEMPLATE_DIR = BASE_DIR / 'jj_templates'
for d in (UPLOAD_DIR, RENDER_DIR, TEMPLATE_DIR): d.mkdir(parents=True, exist_ok=True)

MAX_PHOTOS = 10
MAX_UPLOAD_MB = 15

# --- Anti-DoS: batasi render berat (ffmpeg/PIL) ---
# Cegah satu/banyak user menghabiskan CPU/disk VPS lewat spam render.
Image.MAX_IMAGE_PIXELS = 40_000_000  # guard decompression bomb
_MAX_CONCURRENT_RENDERS = 2
_RENDER_COOLDOWN = 8  # detik antar render per user
_render_semaphore = asyncio.Semaphore(_MAX_CONCURRENT_RENDERS)
_user_inflight = set()      # user_id yang sedang render
_user_last_render = {}      # user_id -> timestamp render terakhir


def _render_gate(user_id):
    """Return pesan penolakan bila user harus menunggu, atau None bila boleh lanjut."""
    now = time.time()
    if user_id in _user_inflight:
        return "Permintaan sebelumnya masih diproses. Tunggu sebentar."
    last = _user_last_render.get(user_id, 0)
    if now - last < _RENDER_COOLDOWN:
        wait = int(_RENDER_COOLDOWN - (now - last)) + 1
        return f"Tunggu {wait} detik sebelum render lagi."
    return None


async def _run_render(user_id, make_coro):
    """Jalankan render dengan batas konkurensi global + tandai user sedang sibuk."""
    _user_inflight.add(user_id)
    try:
        async with _render_semaphore:
            return await make_coro()
    finally:
        _user_inflight.discard(user_id)
        _user_last_render[user_id] = time.time()


async def _creative_allowed(update, context):
    """Gate ringan: butuh subscribe channel (samakan dengan alur menfess).
    Fail-closed mengikuti perilaku is_subscribed yang sudah menangani exception."""
    try:
        from randomunderground_bot import is_subscribed
    except Exception:
        return True  # jika modul utama tak tersedia, jangan blokir
    try:
        return await is_subscribed(update.effective_user.id, context)
    except Exception:
        return False
JJ_PRESETS = {
    'cute': ('STATIC', 0.62),
    'flash': ('STROBE', 0.48),
    'dark': ('DARK', 0.58),
    'y2k': ('Y2K', 0.52),
    'cinematic': ('CINEMATIC', 0.82),
    'velocity': ('VELOCITY', 0.42),
}

# ---------- shared helpers ----------
def _ffmpeg():
    return shutil.which('ffmpeg')

def _safe_name(s):
    return re.sub(r'[^a-zA-Z0-9_-]+', '_', s)[:60]

def _font(size=52, bold=False):
    candidates = [
        '/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf' if bold else '/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf',
        '/usr/share/fonts/truetype/liberation2/LiberationSans-Bold.ttf' if bold else '/usr/share/fonts/truetype/liberation2/LiberationSans-Regular.ttf'
    ]
    for p in candidates:
        if os.path.exists(p): return ImageFont.truetype(p, size)
    return ImageFont.load_default()

def _fit(img, size):
    return ImageOps.fit(img.convert('RGB'), size, method=Image.Resampling.LANCZOS, centering=(0.5,0.5))

def _save_photo_bytes(data, path):
    im = Image.open(io.BytesIO(data)).convert('RGB')
    if im.width * im.height > 30_000_000:
        im.thumbnail((5000,5000), Image.Resampling.LANCZOS)
    im.save(path, quality=94)

def _run(cmd, timeout=120):
    p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
    if p.returncode != 0:
        raise RuntimeError(p.stderr.decode(errors='ignore')[-2500:])

async def _download_photo(bot, file_id, dest):
    f = await bot.get_file(file_id)
    await f.download_to_drive(custom_path=str(dest))
    if dest.stat().st_size > MAX_UPLOAD_MB * 1024 * 1024:
        dest.unlink(missing_ok=True); raise ValueError('File terlalu besar.')

# ---------- menus ----------
def creative_menu():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton('▪ JJ MAKER', callback_data='creative:jj')],
        [InlineKeyboardButton('▪ PHOTO TOOLS', callback_data='creative:photo')],
        [InlineKeyboardButton('▪ FUN', callback_data='creative:fun')],
        [InlineKeyboardButton('▪ TEXT TOOLS', callback_data='creative:text')],
    ])

def jj_menu():
    rows=[]
    for k,(name,_) in JJ_PRESETS.items(): rows.append([InlineKeyboardButton(name, callback_data=f'jj:{k}')])
    rows.append([InlineKeyboardButton('↩️ CREATIVE', callback_data='creative:home')])
    return InlineKeyboardMarkup(rows)

def photo_menu():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton('▪ POLAROID', callback_data='photo:polaroid'), InlineKeyboardButton('▪ PHOTO DUMP', callback_data='photo:dump')],
        [InlineKeyboardButton('▪ STICKER', callback_data='photo:sticker'), InlineKeyboardButton('▪ MEME', callback_data='photo:meme')],
        [InlineKeyboardButton('↩️ CREATIVE', callback_data='creative:home')],
    ])

async def creative_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data['creative_mode'] = None
    await update.message.reply_text(
        'RANDOM UNDERGROUND // CREATIVE\n\nBikin JJ, edit foto, atau cari ide teks. Pilih modul:',
        reply_markup=creative_menu())

async def jj_command(update, context):
    context.user_data['creative_mode'] = 'jj_choose'
    await update.message.reply_text('RANDOM UNDERGROUND // JJ MAKER\n\nPilih style:', reply_markup=jj_menu())

async def creative_callback(update, context):
    q=update.callback_query; await q.answer(); data=q.data
    if data == 'creative:home':
        context.user_data['creative_mode']=None; await q.edit_message_text('RANDOM UNDERGROUND // CREATIVE', reply_markup=creative_menu()); return
    if data == 'creative:jj':
        context.user_data['creative_mode']='jj_choose'; await q.edit_message_text('PILIH TEMPLATE JJ', reply_markup=jj_menu()); return
    if data == 'creative:photo':
        await q.edit_message_text('PHOTO TOOLS', reply_markup=photo_menu()); return
    if data == 'creative:fun':
        await q.edit_message_text('FUN\n\n/8ball\n/rate @user\n/ship @a @b\n/truthordare\n/wyr', reply_markup=creative_menu()); return
    if data == 'creative:text':
        await q.edit_message_text('TEXT TOOLS\n\n/caption\n/bio\n/username\n/quote', reply_markup=creative_menu()); return
    if data.startswith('jj:'):
        preset=data.split(':',1)[1]
        context.user_data['creative_mode']='jj_upload'
        context.user_data['jj_preset']=preset; context.user_data['jj_photos']=[]
        await q.edit_message_text(f'{JJ_PRESETS[preset][0]}\n\n▸ Kirim 2–10 foto berurutan.\n▸ Ketik /done setelah selesai.'); return
    if data.startswith('photo:'):
        mode=data.split(':',1)[1]; context.user_data['creative_mode']=mode
        await q.edit_message_text('▸ Kirim 1 foto sekarang.'); return

# ---------- JJ renderer ----------
def _make_clip(image_path, out_path, duration, preset, index):
    # Each clip gets a different subtle motion; FFmpeg handles the animation.
    if preset == 'cinematic':
        vf=f"scale=1080:1920:force_original_aspect_ratio=increase,crop=1080:1920,zoompan=z='min(zoom+0.0008,1.10)':d=1:s=1080x1920:fps=30,eq=saturation=0.88:contrast=1.04,fade=t=in:st=0:d=0.18"
    elif preset == 'dark':
        vf=f"scale=1080:1920:force_original_aspect_ratio=increase,crop=1080:1920,zoompan=z='min(zoom+0.0012,1.12)':d=1:s=1080x1920:fps=30,eq=brightness=-0.04:saturation=0.92:contrast=1.10,fade=t=in:st=0:d=0.10"
    elif preset == 'y2k':
        vf=f"scale=1080:1920:force_original_aspect_ratio=increase,crop=1080:1920,zoompan=z='min(zoom+0.0015,1.14)':d=1:s=1080x1920:fps=30,eq=saturation=1.22:contrast=1.06,fade=t=in:st=0:d=0.08"
    elif preset == 'velocity':
        vf=f"scale=1080:1920:force_original_aspect_ratio=increase,crop=1080:1920,zoompan=z='min(zoom+0.002,1.18)':d=1:s=1080x1920:fps=30,eq=saturation=1.08:contrast=1.05"
    elif preset == 'flash':
        vf=f"scale=1080:1920:force_original_aspect_ratio=increase,crop=1080:1920,zoompan=z='min(zoom+0.0017,1.15)':d=1:s=1080x1920:fps=30,eq=saturation=1.10:contrast=1.05,fade=t=in:st=0:d=0.06"
    else:
        vf=f"scale=1080:1920:force_original_aspect_ratio=increase,crop=1080:1920,zoompan=z='min(zoom+0.0013,1.13)':d=1:s=1080x1920:fps=30,eq=saturation=1.06"
    frames=max(1, int(duration*30))
    vf=vf.replace(':d=1:', f':d={frames}:')
    _run([_ffmpeg(),'-y','-loop','1','-i',str(image_path),'-t',str(duration),'-vf',vf,'-an','-c:v','libx264','-preset','veryfast','-pix_fmt','yuv420p',str(out_path)], timeout=60)

def render_jj(paths, preset, audio=None):
    if not _ffmpeg(): raise RuntimeError('FFmpeg belum terpasang di VPS.')
    uid=_safe_name(str(random.randrange(10**9)))
    work=RENDER_DIR/f'job_{uid}'; work.mkdir()
    clips=[]
    dur=JJ_PRESETS[preset][1]
    try:
        for i,p in enumerate(paths):
            clip=work/f'c{i}.mp4'; _make_clip(p,clip,dur,preset,i); clips.append(clip)
        concat=work/'list.txt'
        concat.write_text('\n'.join(f"file '{c.as_posix()}'" for c in clips), encoding='utf8')
        silent=work/'silent.mp4'
        _run([_ffmpeg(),'-y','-f','concat','-safe','0','-i',str(concat),'-c','copy',str(silent)], timeout=120)
        out=RENDER_DIR/f'JJ_{uid}.mp4'
        if audio and Path(audio).exists():
            _run([_ffmpeg(),'-y','-i',str(silent),'-stream_loop','-1','-i',str(audio),'-shortest','-map','0:v:0','-map','1:a:0','-c:v','copy','-c:a','aac','-b:a','192k',str(out)], timeout=120)
        else:
            shutil.copy2(silent,out)
        return out
    finally:
        shutil.rmtree(work, ignore_errors=True)

async def jjmusic_command(update, context):
    if context.user_data.get('creative_mode') != 'jj_upload':
        await update.message.reply_text('Mulai /jj dulu.')
        return
    context.user_data['jj_wait_audio'] = True
    await update.message.reply_text('▸ Kirim file audio (MP3/M4A) yang kamu punya hak untuk gunakan. Setelah itu lanjut kirim foto dan /done.')

async def audio_handler(update, context):
    if not update.message or not update.message.audio or not context.user_data.get('jj_wait_audio'):
        return False
    a=update.message.audio
    path=UPLOAD_DIR/f"{update.effective_user.id}_{random.randrange(10**9)}.mp3"
    f=await context.bot.get_file(a.file_id); await f.download_to_drive(custom_path=str(path))
    context.user_data['jj_audio']=str(path); context.user_data['jj_wait_audio']=False
    await update.message.reply_text('Audio tersimpan. Sekarang kirim 2–10 foto lalu /done.')
    return True

async def done_command(update, context):
    if context.user_data.get('creative_mode') != 'jj_upload': return
    paths=context.user_data.get('jj_photos',[])
    if len(paths)<2:
        await update.message.reply_text('Minimal 2 foto.'); return
    gate=_render_gate(update.effective_user.id)
    if gate:
        await update.message.reply_text(gate); return
    await update.message.reply_text('Merender JJ. Jangan tutup chat.')
    try:
        out=await _run_render(update.effective_user.id, lambda: asyncio.to_thread(render_jj, paths, context.user_data['jj_preset'], context.user_data.get('jj_audio')))
        await update.message.reply_video(video=out.open('rb'), caption=f"JJ SELESAI\nTemplate: {JJ_PRESETS[context.user_data['jj_preset']][0]}")
    except Exception as e:
        await update.message.reply_text(f'✕ JJ gagal dibuat: {str(e)[:500]}')
    finally:
        for p in paths:
            Path(p).unlink(missing_ok=True)
        context.user_data.pop('jj_photos',None); context.user_data['creative_mode']=None
        if context.user_data.get('jj_audio'):
            Path(context.user_data['jj_audio']).unlink(missing_ok=True)
        context.user_data.pop('jj_audio',None); context.user_data.pop('jj_wait_audio',None)

async def creative_photo_handler(update, context):
    if not update.message or not update.message.photo: return False
    mode=context.user_data.get('creative_mode')
    if mode == 'jj_upload':
        if not await _creative_allowed(update, context):
            await update.message.reply_text('✕ Subscribe channel RANDOM UNDERGROUND dulu sebelum pakai fitur creative.'); return True
        paths=context.user_data.setdefault('jj_photos',[])
        if len(paths)>=MAX_PHOTOS:
            await update.message.reply_text('Maksimal 10 foto. Ketik /done.'); return True
        path=UPLOAD_DIR/f"{update.effective_user.id}_{random.randrange(10**9)}.jpg"
        await _download_photo(context.bot, update.message.photo[-1].file_id, path)
        paths.append(str(path)); await update.message.reply_text(f'Foto {len(paths)}/{MAX_PHOTOS} diterima. Kirim lagi atau /done.'); return True
    if mode in {'polaroid','dump','sticker','meme'}:
        if not await _creative_allowed(update, context):
            await update.message.reply_text('✕ Subscribe channel RANDOM UNDERGROUND dulu sebelum pakai fitur creative.'); return True
        gate=_render_gate(update.effective_user.id)
        if gate:
            await update.message.reply_text(gate); return True
        path=UPLOAD_DIR/f"{update.effective_user.id}_{random.randrange(10**9)}.jpg"
        try: await _download_photo(context.bot, update.message.photo[-1].file_id, path)
        except Exception as e: await update.message.reply_text(str(e)); return True
        try:
            out=await _run_render(update.effective_user.id, lambda: asyncio.to_thread(render_photo_tool,path,mode,context.user_data.get('meme_text','')))
            if mode=='sticker': await update.message.reply_sticker(sticker=out.open('rb'))
            else: await update.message.reply_photo(photo=out.open('rb'), caption='RANDOM UNDERGROUND')
        finally:
            path.unlink(missing_ok=True)
            if 'out' in locals(): out.unlink(missing_ok=True)
        context.user_data['creative_mode']=None; return True
    return False

# ---------- photo tools ----------
def render_photo_tool(path, mode, text=''):
    im=Image.open(path).convert('RGBA')
    if mode=='polaroid':
        photo=_fit(im,(900,900)); canvas=Image.new('RGBA',(1000,1150),'white'); canvas.alpha_composite(photo,(50,50)); d=ImageDraw.Draw(canvas); d.text((500,1010),'RANDOM UNDERGROUND',font=_font(38),fill='black',anchor='mm'); out=RENDER_DIR/f'{random.randrange(10**9)}.png'; canvas.save(out); return out
    if mode=='dump':
        photo=_fit(im,(1080,1080)); canvas=Image.new('RGBA',(1080,1350),(245,240,238,255)); canvas.alpha_composite(photo,(0,0)); d=ImageDraw.Draw(canvas); d.text((54,1140),'PHOTO DUMP  /  RANDOM UNDERGROUND',font=_font(34),fill=(35,35,35),stroke_width=1); out=RENDER_DIR/f'{random.randrange(10**9)}.png'; canvas.save(out); return out
    if mode=='sticker':
        im.thumbnail((900,900),Image.Resampling.LANCZOS); bg=Image.new('RGBA',(1024,1024),(255,255,255,0)); x=(1024-im.width)//2; y=(1024-im.height)//2; bg.alpha_composite(im,(x,y)); out=RENDER_DIR/f'{random.randrange(10**9)}.webp'; bg.save(out,'WEBP',lossless=True); return out
    if mode=='meme':
        photo=_fit(im,(1080,1080)); canvas=Image.new('RGB',(1080,1280),'white'); canvas.paste(photo,(0,0)); d=ImageDraw.Draw(canvas); txt=(text or 'WHEN YOU SAY CUMA LIHAT-LIHAT').upper(); d.text((540,1180),txt,font=_font(40,True),fill='black',anchor='mm'); out=RENDER_DIR/f'{random.randrange(10**9)}.jpg'; canvas.save(out,quality=94); return out
    raise ValueError('Mode tidak dikenal')

async def pfp_command(update,context): context.user_data['creative_mode']='dump'; await update.message.reply_text('▸ Kirim foto untuk PFP 1:1.');
async def story_command(update,context): context.user_data['creative_mode']='dump'; await update.message.reply_text('▸ Kirim foto untuk Story.');
async def polaroid_command(update,context): context.user_data['creative_mode']='polaroid'; await update.message.reply_text('▸ Kirim fotonya.')
async def dump_command(update,context): context.user_data['creative_mode']='dump'; await update.message.reply_text('▸ Kirim fotonya.')
async def sticker_command(update,context): context.user_data['creative_mode']='sticker'; await update.message.reply_text('▸ Kirim foto untuk dibuat sticker.')
async def meme_command(update,context):
    context.user_data['creative_mode']='meme'; context.user_data['meme_text']=''
    await update.message.reply_text('▸ Kirim foto. Setelah itu kamu bisa tambahkan teks di /meme <teks>.')

async def image_simple(update,context,mode):
    if not update.message or not update.message.photo: await update.message.reply_text('▸ Kirim foto setelah command ini.'); return
    path=UPLOAD_DIR/f"{update.effective_user.id}_{random.randrange(10**9)}.jpg"; await _download_photo(context.bot,update.message.photo[-1].file_id,path)
    try:
        im=Image.open(path).convert('RGB')
        if mode=='resize': im.thumbnail((1080,1080),Image.Resampling.LANCZOS)
        elif mode=='compress': im.thumbnail((1800,1800),Image.Resampling.LANCZOS)
        elif mode=='square': im=ImageOps.fit(im,(1080,1080))
        elif mode=='story': im=ImageOps.fit(im,(1080,1920))
        out=RENDER_DIR/f'{random.randrange(10**9)}.jpg'; im.save(out,quality=82,optimize=True); await update.message.reply_photo(photo=out.open('rb'),caption='RANDOM UNDERGROUND // PHOTO TOOL')
    finally: path.unlink(missing_ok=True); out.unlink(missing_ok=True)

# ---------- fun ----------
async def eightball(update,context):
    answers=['IYA.','JANGAN.','KAYAKNYA.','GAS.','TANYA LAGI NANTI.','YES.','MENDING TIDUR.']; await update.message.reply_text('8BALL\n\n'+random.choice(answers))
async def rate(update,context): await update.message.reply_text(f'RATE\n\n{random.randint(1,100)}% cocok jadi main character hari ini.')
async def ship(update,context):
    names=context.args if len(context.args)>=2 else ['Kamu','Someone']; await update.message.reply_text(f'{names[0]} × {names[1]}\n\nCompatibility: {random.randint(1,100)}%')
async def truthordare(update,context): await update.message.reply_text('TRUTH OR DARE\n\nTruth: siapa yang terakhir kamu stalk?\n\natau\n\nDare: kirim foto terakhir di galeri tanpa konteks.')
async def wyr(update,context): await update.message.reply_text('WOULD YOU RATHER\n\nA. Punya barang incaran tapi nggak boleh beli 1 tahun\nB. Boleh checkout bebas tapi nggak boleh menyesal.\n\nA atau B?')

# ---------- text ----------
CAPTIONS=['no context, just vibes.','proof that today happened.','archive footage.','low light, high noise.','unlisted. undated.','found this in the drafts.']
BIOS=['offline more than online','here for the plot','made of playlists and late nights','no caption needed','signal weak, still transmitting']
async def caption(update,context): await update.message.reply_text('CAPTION\n\n'+random.choice(CAPTIONS))
async def bio(update,context): await update.message.reply_text('BIO\n\n'+random.choice(BIOS))
async def username(update,context):
    a=['void','static','grain','noise','dusk','mono','ash','vhs']; b=['archive','jpg','core','files','room','era','tape']; await update.message.reply_text('USERNAME\n\n@'+random.choice(a)+random.choice(b)+str(random.randint(0,99)))
async def quote(update,context): await update.message.reply_text('“Some things are better felt than explained.”')

# ---------- handler registration ----------
def register_creative_handlers(app):
    from telegram.ext import CommandHandler, CallbackQueryHandler, MessageHandler, filters
    app.add_handler(CommandHandler('creative',creative_command))
    app.add_handler(CommandHandler('jj',jj_command))
    app.add_handler(CommandHandler('done',done_command))
    app.add_handler(CommandHandler('jjmusic',jjmusic_command))
    app.add_handler(CommandHandler('pfp',pfp_command))
    app.add_handler(CommandHandler('story',story_command))
    app.add_handler(CommandHandler('polaroid',polaroid_command))
    app.add_handler(CommandHandler('photodump',dump_command))
    app.add_handler(CommandHandler('sticker',sticker_command))
    app.add_handler(CommandHandler('meme',meme_command))
    app.add_handler(CommandHandler('8ball',eightball))
    app.add_handler(CommandHandler('rate',rate))
    app.add_handler(CommandHandler('ship',ship))
    app.add_handler(CommandHandler('truthordare',truthordare))
    app.add_handler(CommandHandler('wyr',wyr))
    app.add_handler(CommandHandler('caption',caption))
    app.add_handler(CommandHandler('bio',bio))
    app.add_handler(CommandHandler('username',username))
    app.add_handler(CommandHandler('quote',quote))
    app.add_handler(CallbackQueryHandler(creative_callback,pattern=r'^(creative|jj|photo):'))
    app.add_handler(MessageHandler(filters.ChatType.PRIVATE & filters.AUDIO, audio_handler), group=0)
    app.add_handler(MessageHandler(filters.ChatType.PRIVATE & filters.PHOTO, creative_photo_handler), group=0)
