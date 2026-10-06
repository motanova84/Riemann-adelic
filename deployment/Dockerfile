FROM python:3.11-slim

ENV PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    QCAL_EXPECTED_SENDER=127.0.0.1

WORKDIR /app
COPY deployment/requirements.txt /app/deployment/requirements.txt
RUN pip install --no-cache-dir --only-binary=:all: -r deployment/requirements.txt
COPY --chown=10001:10001 experiments /app/experiments
COPY --chown=10001:10001 experimental_validation /app/experimental_validation

USER 10001:10001
EXPOSE 8050/tcp 5005/udp
HEALTHCHECK --interval=10s --timeout=3s --start-period=10s --retries=3 \
    CMD python -c "import urllib.request; urllib.request.urlopen('http://127.0.0.1:8050/health', timeout=2)"
# LAN acquisition requires -e QCAL_EXPECTED_SENDER=<sender-IP>.
CMD ["python", "-m", "experiments.qcal_exp01.dashboard", "--host", "0.0.0.0", "--udp-host", "0.0.0.0", "--allow-lan", "--port", "8050", "--udp-port", "5005"]
