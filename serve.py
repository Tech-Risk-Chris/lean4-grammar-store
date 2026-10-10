#!/usr/bin/env python3
"""HTTP front for grammar-store: one long-lived process, one session, requests serialised.

    python3 serve.py [path/to/grammar-store] [port]
    curl -d 'check She teached us.' localhost:8080
"""
import subprocess, sys, threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

BIN  = sys.argv[1] if len(sys.argv) > 1 else ".lake/build/bin/grammar-store"
PORT = int(sys.argv[2]) if len(sys.argv) > 2 else 8080

proc = subprocess.Popen([BIN], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
lock = threading.Lock()

def run(cmd: str) -> str:
    cmd = " ".join(cmd.split()) or "help"      # one non-empty line; empty would read as EOF
    with lock:
        proc.stdin.write(cmd + "\n")
        proc.stdin.flush()
        out = []
        for line in proc.stdout:
            if line.rstrip("\n") == ".":
                break
            out.append(line)
        return "".join(out)

class Handler(BaseHTTPRequestHandler):
    def do_POST(self):
        n = int(self.headers.get("Content-Length", 0))
        data = run(self.rfile.read(n).decode("utf-8")).encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "text/plain; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

ThreadingHTTPServer(("127.0.0.1", PORT), Handler).serve_forever()
