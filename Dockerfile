FROM python:3.11-slim

# ffmpeg dibutuhkan oleh modul creative (JJ maker). fonts untuk PIL drawtext.
RUN apt-get update \
    && apt-get install -y --no-install-recommends ffmpeg fonts-dejavu-core \
    && rm -rf /var/lib/apt/lists/*

# stdout tidak di-buffer, supaya banner startup (termasuk tujuan log channel)
# langsung terlihat di "docker logs", bukan tertahan sampai buffer penuh.
ENV PYTHONUNBUFFERED=1

WORKDIR /app

COPY requirements_randomunderground.txt ./requirements.txt
RUN pip install --no-cache-dir -r requirements.txt

COPY . .

# Jalankan sebagai non-root.
RUN useradd -m -u 10001 appuser && chown -R appuser:appuser /app
USER appuser

# JANGAN hardcode token. Inject saat runtime:
#   docker run -e RANDOMUNDERGROUND_BOT_TOKEN=xxxxx ...
# atau gunakan docker secrets / env_file yang tidak ikut ter-commit.
CMD ["python3", "randomunderground_bot.py"]
