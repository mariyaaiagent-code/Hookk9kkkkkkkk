import http.server
import socketserver
import os
import sqlite3
import json

PORT = int(os.getenv("PORT", 3000))
DB_FILE = os.getenv("BOT_DB_FILE", "bot_data.db")

class Handler(http.server.SimpleHTTPRequestHandler):
    def do_GET(self):
        if self.path == "/health":
            self.send_response(200)
            self.send_header("Content-type", "application/json")
            self.end_headers()
            self.wfile.write(b'{"status":"healthy","bot":"OTP ZONE"}')
            return

        self.send_response(200)
        self.send_header("Content-type", "text/html; charset=utf-8")
        self.end_headers()

        # Gather stats from sqlite db if available
        users_count = 0
        numbers_count = 0
        panels_count = 0
        traffic_count = 0
        panels = []
        recent_traffic = []

        try:
            if os.path.exists(DB_FILE):
                conn = sqlite3.connect(DB_FILE)
                conn.row_factory = sqlite3.Row
                cursor = conn.cursor()
                
                try:
                    res = cursor.fetchone()
                    if res: users_count = res[0]
                except: pass

                try:
                    res = cursor.execute("SELECT COUNT(*) FROM numbers").fetchone()
                    if res: numbers_count = res[0]
                except: pass

                try:
                    res = cursor.execute("SELECT COUNT(*) FROM panels").fetchone()
                    if res: panels_count = res[0]
                except: pass

                try:
                    res = cursor.execute("SELECT COUNT(*) FROM traffic_events").fetchone()
                    if res: traffic_count = res[0]
                except: pass

                try:
                    panels = [dict(row) for row in cursor.execute("SELECT id, name, login_url, active FROM panels LIMIT 10").fetchall()]
                except: pass

                try:
                    recent_traffic = [dict(row) for row in cursor.execute("SELECT occurred_at, service_name, country_name, iso2 FROM traffic_events ORDER BY id DESC LIMIT 10").fetchall()]
                except: pass

                conn.close()
        except Exception as e:
            print(f"Dashboard DB error: {e}")

        html = f"""<!DOCTYPE html>
<html lang="en" class="dark">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>OTP ZONE - Bot Management Dashboard</title>
    <script src="https://cdn.jsdelivr.net/npm/@tailwindcss/browser@4"></script>
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.4.0/css/all.min.css">
</head>
<body class="bg-slate-950 text-slate-100 min-h-screen font-sans antialiased">
    <div class="flex h-screen overflow-hidden">
        <!-- Sidebar -->
        <aside class="w-64 bg-slate-900 border-r border-slate-800 flex flex-col hidden md:flex">
            <div class="p-6 border-b border-slate-800 flex items-center space-x-3">
                <div class="w-10 h-10 rounded-xl bg-gradient-to-tr from-cyan-500 to-indigo-600 flex items-center justify-center shadow-lg shadow-cyan-500/30">
                    <i class="fa-solid fa-shield-halved text-white text-lg"></i>
                </div>
                <div>
                    <h1 class="font-bold text-lg tracking-wider text-white">𝗢𝗧𝗣 𝗭𝗢𝗡𝗘</h1>
                    <span class="text-xs text-cyan-400 font-medium">Telegram Bot Admin</span>
                </div>
            </div>
            <nav class="flex-1 p-4 space-y-2">
                <a href="#" class="flex items-center space-x-3 px-4 py-3 rounded-lg bg-cyan-500/10 text-cyan-400 font-medium border border-cyan-500/20">
                    <i class="fa-solid fa-chart-pie w-5"></i>
                    <span>Dashboard</span>
                </a>
                <a href="https://t.me/OtpZoneAZ_Bot" target="_blank" class="flex items-center space-x-3 px-4 py-3 rounded-lg text-slate-400 hover:bg-slate-800 hover:text-slate-200 transition">
                    <i class="fa-brands fa-telegram w-5 text-sky-400"></i>
                    <span>Open Bot</span>
                </a>
                <a href="https://t.me/EarnAirdropX" target="_blank" class="flex items-center space-x-3 px-4 py-3 rounded-lg text-slate-400 hover:bg-slate-800 hover:text-slate-200 transition">
                    <i class="fa-solid fa-bullhorn w-5 text-indigo-400"></i>
                    <span>Channel</span>
                </a>
                <a href="https://t.me/buysellxgroup" target="_blank" class="flex items-center space-x-3 px-4 py-3 rounded-lg text-slate-400 hover:bg-slate-800 hover:text-slate-200 transition">
                    <i class="fa-solid fa-comments w-5 text-emerald-400"></i>
                    <span>Discussion Group</span>
                </a>
            </nav>
            <div class="p-4 border-t border-slate-800 text-xs text-slate-500 text-center">
                Firebase Project: <span class="text-slate-300">otp-group-8bf7e</span>
            </div>
        </aside>

        <!-- Main Content -->
        <main class="flex-1 flex flex-col overflow-y-auto">
            <!-- Top Header -->
            <header class="h-20 bg-slate-900/50 backdrop-blur border-b border-slate-800 px-8 flex items-center justify-between">
                <div>
                    <h2 class="text-2xl font-bold text-white flex items-center gap-2">
                        <span>𝗢𝗧𝗣 𝗭𝗢𝗡𝗘 Control Center</span>
                        <span class="text-xs bg-emerald-500/20 text-emerald-400 border border-emerald-500/30 px-2.5 py-1 rounded-full">● Live</span>
                    </h2>
                    <p class="text-sm text-slate-400">Automated number provisioning & OTP forwarding system</p>
                </div>
                <div class="flex items-center space-x-4">
                    <a href="https://t.me/OtpZoneAZ_Bot" target="_blank" class="bg-cyan-600 hover:bg-cyan-500 text-white px-4 py-2 rounded-lg font-medium shadow-lg shadow-cyan-600/20 transition flex items-center gap-2 text-sm">
                        <i class="fa-brands fa-telegram"></i> Launch Bot
                    </a>
                </div>
            </header>

            <!-- Content Body -->
            <div class="p-8 space-y-8">
                <!-- Stats Grid -->
                <div class="grid grid-cols-1 md:grid-cols-4 gap-6">
                    <div class="bg-slate-900 border border-slate-800 rounded-2xl p-6 shadow-xl">
                        <div class="flex items-center justify-between">
                            <span class="text-slate-400 text-sm font-medium">Total Users</span>
                            <div class="w-10 h-10 rounded-xl bg-blue-500/10 text-blue-400 flex items-center justify-center">
                                <i class="fa-solid fa-users text-lg"></i>
                            </div>
                        </div>
                        <div class="mt-4 flex items-baseline">
                            <span class="text-3xl font-extrabold text-white">{users_count}</span>
                            <span class="ml-2 text-xs text-emerald-400 font-semibold">Active</span>
                        </div>
                    </div>

                    <div class="bg-slate-900 border border-slate-800 rounded-2xl p-6 shadow-xl">
                        <div class="flex items-center justify-between">
                            <span class="text-slate-400 text-sm font-medium">Phone Numbers</span>
                            <div class="w-10 h-10 rounded-xl bg-emerald-500/10 text-emerald-400 flex items-center justify-center">
                                <i class="fa-solid fa-phone text-lg"></i>
                            </div>
                        </div>
                        <div class="mt-4 flex items-baseline">
                            <span class="text-3xl font-extrabold text-white">{numbers_count}</span>
                            <span class="ml-2 text-xs text-emerald-400 font-semibold">In Inventory</span>
                        </div>
                    </div>

                    <div class="bg-slate-900 border border-slate-800 rounded-2xl p-6 shadow-xl">
                        <div class="flex items-center justify-between">
                            <span class="text-slate-400 text-sm font-medium">Active Panels</span>
                            <div class="w-10 h-10 rounded-xl bg-purple-500/10 text-purple-400 flex items-center justify-center">
                                <i class="fa-solid fa-server text-lg"></i>
                            </div>
                        </div>
                        <div class="mt-4 flex items-baseline">
                            <span class="text-3xl font-extrabold text-white">{panels_count}</span>
                            <span class="ml-2 text-xs text-purple-400 font-semibold">Online</span>
                        </div>
                    </div>

                    <div class="bg-slate-900 border border-slate-800 rounded-2xl p-6 shadow-xl">
                        <div class="flex items-center justify-between">
                            <span class="text-slate-400 text-sm font-medium">OTP Events Logged</span>
                            <div class="w-10 h-10 rounded-xl bg-amber-500/10 text-amber-400 flex items-center justify-center">
                                <i class="fa-solid fa-bolt text-lg"></i>
                            </div>
                        </div>
                        <div class="mt-4 flex items-baseline">
                            <span class="text-3xl font-extrabold text-white">{traffic_count}</span>
                            <span class="ml-2 text-xs text-amber-400 font-semibold">Total</span>
                        </div>
                    </div>
                </div>

                <!-- Quick Links Banner -->
                <div class="bg-gradient-to-r from-cyan-900/40 via-indigo-900/40 to-slate-900 border border-cyan-500/20 rounded-2xl p-6 flex flex-col md:flex-row items-center justify-between gap-4 shadow-xl">
                    <div class="space-y-1 text-center md:text-left">
                        <h3 class="text-lg font-bold text-white flex items-center justify-center md:justify-start gap-2">
                            <span>Official Telegram Channels & Bot</span>
                        </h3>
                        <p class="text-sm text-slate-300">Join our community channel for updates and connect with the bot instantly.</p>
                    </div>
                    <div class="flex flex-wrap gap-3">
                        <a href="https://t.me/OtpZoneAZ_Bot" target="_blank" class="bg-sky-500 hover:bg-sky-400 text-slate-950 font-bold px-5 py-2.5 rounded-xl transition flex items-center gap-2 shadow-lg shadow-sky-500/20">
                            <i class="fa-brands fa-telegram"></i> @OtpZoneAZ_Bot
                        </a>
                        <a href="https://t.me/EarnAirdropX" target="_blank" class="bg-indigo-600 hover:bg-indigo-500 text-white font-bold px-5 py-2.5 rounded-xl transition flex items-center gap-2 shadow-lg shadow-indigo-600/20">
                            <i class="fa-solid fa-bullhorn"></i> Channel
                        </a>
                        <a href="https://t.me/buysellxgroup" target="_blank" class="bg-emerald-600 hover:bg-emerald-500 text-white font-bold px-5 py-2.5 rounded-xl transition flex items-center gap-2 shadow-lg shadow-emerald-600/20">
                            <i class="fa-solid fa-comments"></i> Group
                        </a>
                    </div>
                </div>

                <!-- Two Column Details -->
                <div class="grid grid-cols-1 lg:grid-cols-2 gap-8">
                    <!-- Panels Table -->
                    <div class="bg-slate-900 border border-slate-800 rounded-2xl p-6 shadow-xl flex flex-col">
                        <div class="flex items-center justify-between mb-4">
                            <h3 class="font-bold text-lg text-white flex items-center gap-2">
                                <i class="fa-solid fa-network-wired text-cyan-400"></i> Connected Panels
                            </h3>
                            <span class="text-xs bg-slate-800 text-slate-300 px-3 py-1 rounded-full font-medium">Sync Active</span>
                        </div>
                        <div class="overflow-x-auto flex-1">
                            <table class="w-full text-left text-sm text-slate-300">
                                <thead class="border-b border-slate-800 text-xs uppercase text-slate-400">
                                    <tr>
                                        <th class="py-3 px-4">Panel Name</th>
                                        <th class="py-3 px-4">URL</th>
                                        <th class="py-3 px-4">Status</th>
                                    </tr>
                                </thead>
                                <tbody class="divide-y divide-slate-800/60">
"""

        if panels:
            for p in panels:
                status_badge = '<span class="text-emerald-400 bg-emerald-500/10 px-2 py-0.5 rounded text-xs font-semibold">Active</span>' if p.get('active') else '<span class="text-amber-400 bg-amber-500/10 px-2 py-0.5 rounded text-xs font-semibold">Paused</span>'
                html += f"""
                                    <tr class="hover:bg-slate-800/40">
                                        <td class="py-3 px-4 font-medium text-white">{p.get('name')}</td>
                                        <td class="py-3 px-4 text-slate-400 truncate max-w-xs">{p.get('login_url')}</td>
                                        <td class="py-3 px-4">{status_badge}</td>
                                    </tr>
"""
        else:
            html += """
                                    <tr>
                                        <td colspan="3" class="py-6 text-center text-slate-500">No panels configured yet. Add via Telegram bot.</td>
                                    </tr>
"""

        html += f"""
                                </tbody>
                            </table>
                        </div>
                    </div>

                    <!-- Recent OTP / Traffic Events -->
                    <div class="bg-slate-900 border border-slate-800 rounded-2xl p-6 shadow-xl flex flex-col">
                        <div class="flex items-center justify-between mb-4">
                            <h3 class="font-bold text-lg text-white flex items-center gap-2">
                                <i class="fa-solid fa-bolt text-amber-400"></i> Recent OTP Events
                            </h3>
                            <span class="text-xs bg-slate-800 text-slate-300 px-3 py-1 rounded-full font-medium">Realtime</span>
                        </div>
                        <div class="overflow-x-auto flex-1">
                            <table class="w-full text-left text-sm text-slate-300">
                                <thead class="border-b border-slate-800 text-xs uppercase text-slate-400">
                                    <tr>
                                        <th class="py-3 px-4">Time</th>
                                        <th class="py-3 px-4">Service</th>
                                        <th class="py-3 px-4">Country</th>
                                    </tr>
                                </thead>
                                <tbody class="divide-y divide-slate-800/60">
"""

        if recent_traffic:
            for t in recent_traffic:
                html += f"""
                                    <tr class="hover:bg-slate-800/40">
                                        <td class="py-3 px-4 text-slate-400 font-mono text-xs">{str(t.get('occurred_at'))[:19]}</td>
                                        <td class="py-3 px-4 font-medium text-white">{t.get('service_name')}</td>
                                        <td class="py-3 px-4">{t.get('country_name', 'Global')}</td>
                                    </tr>
"""
        else:
            html += """
                                    <tr>
                                        <td colspan="3" class="py-6 text-center text-slate-500">No recent OTP traffic events recorded.</td>
                                    </tr>
"""

        html += f"""
                                </tbody>
                            </table>
                        </div>
                    </div>
                </div>
            </div>
        </main>
    </div>
</body>
</html>
"""
        self.wfile.write(html.encode("utf-8"))

    def log_message(self, format, *args):
        return

if __name__ == "__main__":
    socketserver.TCPServer.allow_reuse_address = True
    with socketserver.TCPServer(("0.0.0.0", PORT), Handler) as httpd:
        print(f"Serving 𝗢𝗧𝗣 𝗭𝗢𝗡𝗘 Dashboard on port {PORT}")
        httpd.serve_forever()
