"""
🔥 Emergency Evacuation Simulator — Optimized & Creative Edition
═══════════════════════════════════════════════════════════════════
Features:
  • Procedural maze generation (iterative backtracker + loop-breaking)
  • Optimized A* with BFS-precomputed heuristic & came_from reconstruction
  • Fire spread via frontier tracking (skips fully-surrounded cells)
  • Dirty-rect canvas rendering (only redraws changed cells)
  • Dark cyberpunk UI with glow effects, particles & smooth animation
  • Speed & fire-intensity sliders, live stats panel
"""

import tkinter as tk
import random
import heapq
import math
import time
from collections import deque


# ═══════════════════════════════════════════════════════════════
#  CONSTANTS & THEME
# ═══════════════════════════════════════════════════════════════

CELL = 24
MAZE_ROWS = 21          # odd for proper wall alignment
MAZE_COLS = 37           # odd for proper wall alignment
INTERP_FRAMES = 5        # smooth-glide sub-frames
INTERP_MS = 25           # ms per interpolation frame

# ── Dark Cyberpunk Palette ────────────────────────────────
C = dict(
    bg          = '#0b0b1a',
    panel       = '#101028',
    wall        = '#1c1c3c',
    wall_hi     = '#2a2a55',
    floor       = '#111127',
    floor_edge  = '#191935',
    agent       = '#00ff41',
    agent_hi    = '#88ffaa',
    agent_glow  = '#003312',
    fire        = ('#ff2200', '#ff4400', '#ff6600', '#ff8800'),
    fire_glow   = '#2a1000',
    exit_on     = '#00fff5',
    exit_off    = '#006666',
    path        = '#d4ff00',
    danger      = ('#111127', '#1a1408', '#251c08', '#3a2510'),
    text        = '#d0d0e0',
    dim         = '#555570',
    accent      = '#ff006e',
    ok          = '#00ff88',
    fail        = '#ff3355',
    btn_bg      = '#1c1c40',
    btn_fg      = '#00fff5',
)


# ═══════════════════════════════════════════════════════════════
#  PROCEDURAL MAZE GENERATOR
# ═══════════════════════════════════════════════════════════════

def generate_maze(rows=MAZE_ROWS, cols=MAZE_COLS, n_fires=5):
    """
    Iterative backtracker maze with deliberate loop-breaking.
    Produces a connected maze with multiple viable escape routes.
    """
    rows = rows if rows % 2 else rows + 1
    cols = cols if cols % 2 else cols + 1
    g = [['#'] * cols for _ in range(rows)]

    # ── Iterative backtracker (avoids recursion-limit issues) ──
    stack = [(1, 1)]
    g[1][1] = '.'
    while stack:
        r, c = stack[-1]
        dirs = [(0, 2), (0, -2), (2, 0), (-2, 0)]
        random.shuffle(dirs)
        carved = False
        for dr, dc in dirs:
            nr, nc = r + dr, c + dc
            if 1 <= nr < rows - 1 and 1 <= nc < cols - 1 and g[nr][nc] == '#':
                g[r + dr // 2][c + dc // 2] = '.'   # carve wall between
                g[nr][nc] = '.'
                stack.append((nr, nc))
                carved = True
                break
        if not carved:
            stack.pop()

    # ── Break walls to create loops → multiple escape paths ──
    for _ in range(rows * cols // 22):
        rr = random.randrange(2, rows - 2)
        cc = random.randrange(2, cols - 2)
        if g[rr][cc] == '#':
            adj = sum(g[rr + dr][cc + dc] == '.'
                      for dr, dc in ((-1, 0), (1, 0), (0, -1), (0, 1)))
            if adj >= 2:
                g[rr][cc] = '.'

    # ── Place start ──
    g[1][1] = 'S'

    # ── Place 2 exits on right & bottom borders ──
    cands = []
    for r in range(1, rows - 1, 2):
        if g[r][cols - 2] == '.':
            cands.append((r, cols - 1))
    for c in range(1, cols - 1, 2):
        if g[rows - 2][c] == '.':
            cands.append((rows - 1, c))
    random.shuffle(cands)
    placed = 0
    for r, c in cands[:2]:
        g[r][c] = 'E'
        placed += 1
    if placed == 0:                       # fallback guarantee
        g[1][cols - 1] = 'E'
        g[1][cols - 2] = '.'

    # ── Scatter fires (far from start) ──
    floors = [(r, c) for r in range(1, rows - 1)
              for c in range(1, cols - 1)
              if g[r][c] == '.' and abs(r - 1) + abs(c - 1) > 8]
    for r, c in random.sample(floors, min(n_fires, len(floors))):
        g[r][c] = 'F'

    return [''.join(row) for row in g]


# ═══════════════════════════════════════════════════════════════
#  MAZE MODEL (optimised)
# ═══════════════════════════════════════════════════════════════

class Maze:
    """
    Stores grid, fire state, and pre-computed BFS heuristic.
    Fire uses a *frontier set* so interior cells are never re-checked.
    """

    def __init__(self, grid):
        self.grid = [list(r) for r in grid]
        self.rows = len(grid)
        self.cols = len(grid[0])
        self.start = None
        self.exits = []
        self.fires = set()
        self.fire_frontier = set()

        for r in range(self.rows):
            for c in range(self.cols):
                ch = self.grid[r][c]
                if ch == 'S':
                    self.start = (r, c)
                    self.grid[r][c] = '.'
                elif ch == 'E':
                    self.exits.append((r, c))
                elif ch == 'F':
                    self.fires.add((r, c))
                    self.grid[r][c] = '.'

        self.fire_frontier = set(self.fires)
        self.exit_dist = self._bfs_from_exits()

    # ── BFS heuristic pre-computation ─────────────────────
    def _bfs_from_exits(self):
        """Multi-source BFS from all exits → dict[(r,c)] = distance."""
        dist = {}
        q = deque()
        for e in self.exits:
            dist[e] = 0
            q.append(e)
        while q:
            r, c = q.popleft()
            for dr, dc in ((-1, 0), (1, 0), (0, -1), (0, 1)):
                nr, nc = r + dr, c + dc
                if (0 <= nr < self.rows and 0 <= nc < self.cols
                        and (nr, nc) not in dist
                        and self.grid[nr][nc] != '#'):
                    dist[(nr, nc)] = dist[(r, c)] + 1
                    q.append((nr, nc))
        return dist

    def valid(self, r, c):
        return (0 <= r < self.rows and 0 <= c < self.cols
                and self.grid[r][c] != '#' and (r, c) not in self.fires)

    def neighbors(self, r, c):
        """Generator: avoids list allocation per call."""
        for dr, dc in ((-1, 0), (1, 0), (0, -1), (0, 1)):
            nr, nc = r + dr, c + dc
            if self.valid(nr, nc):
                yield nr, nc

    # ── Frontier-based fire spread ────────────────────────
    def spread_fire(self, p=0.3):
        """Spread fire only from frontier cells; returns newly-burning set."""
        new = set()
        keep = set()
        for r, c in self.fire_frontier:
            live = False
            for dr, dc in ((-1, 0), (1, 0), (0, -1), (0, 1)):
                nr, nc = r + dr, c + dc
                if (0 <= nr < self.rows and 0 <= nc < self.cols
                        and self.grid[nr][nc] not in ('#', 'E')
                        and (nr, nc) not in self.fires):
                    live = True
                    if random.random() < p:
                        new.add((nr, nc))
            if live:
                keep.add((r, c))
        self.fires |= new
        self.fire_frontier = keep | new
        return new

    # ── Danger heatmap (BFS bounded at depth 5) ──────────
    def danger_map(self):
        dm = {}
        q = deque()
        for f in self.fires:
            dm[f] = 0
            q.append((f, 0))
        while q:
            (r, c), d = q.popleft()
            if d >= 5:
                continue
            for dr, dc in ((-1, 0), (1, 0), (0, -1), (0, 1)):
                nr, nc = r + dr, c + dc
                if (0 <= nr < self.rows and 0 <= nc < self.cols
                        and (nr, nc) not in dm and self.grid[nr][nc] != '#'):
                    dm[(nr, nc)] = d + 1
                    q.append(((nr, nc), d + 1))
        return dm


# ═══════════════════════════════════════════════════════════════
#  A* PATHFINDER (optimised)
# ═══════════════════════════════════════════════════════════════

def a_star(maze, start):
    """
    A* with:
      • O(1) heuristic from pre-computed BFS distance map
      • came_from dict → reconstruct path only at goal (no list copies)
      • integer counter as tie-breaker for stable heap ordering
    """
    if start in maze.exits:
        return [start]
    if start not in maze.exit_dist:
        return None                          # unreachable from any exit

    came = {start: None}
    g = {start: 0}
    cnt = 0
    pq = [(maze.exit_dist[start], cnt, start)]

    while pq:
        _, _, node = heapq.heappop(pq)

        if node in maze.exits:               # goal reached → reconstruct
            path = []
            while node is not None:
                path.append(node)
                node = came[node]
            return path[::-1]

        gn = g[node]
        for nr, nc in maze.neighbors(*node):
            ng = gn + 1
            if ng < g.get((nr, nc), 1 << 30):
                g[(nr, nc)] = ng
                came[(nr, nc)] = node
                cnt += 1
                h = maze.exit_dist.get((nr, nc), 0)
                heapq.heappush(pq, (ng + h, cnt, (nr, nc)))

    return None


# ═══════════════════════════════════════════════════════════════
#  PARTICLE SYSTEM
# ═══════════════════════════════════════════════════════════════

class Spark:
    """Lightweight particle with gravity, fade, and color dimming."""
    __slots__ = ('x', 'y', 'vx', 'vy', 'life', 'ml', 'color', 'sz')

    def __init__(self, x, y, vx, vy, life, color, sz=3):
        self.x, self.y = x, y
        self.vx, self.vy = vx, vy
        self.life = self.ml = life
        self.color = color
        self.sz = sz

    def tick(self):
        self.x += self.vx
        self.y += self.vy
        self.vy += 0.08              # gravity
        self.life -= 1
        return self.life > 0

    def faded_color(self):
        """Dim colour proportional to remaining life."""
        t = max(0.0, self.life / self.ml)
        r = int(int(self.color[1:3], 16) * t)
        g = int(int(self.color[3:5], 16) * t)
        b = int(int(self.color[5:7], 16) * t)
        return f'#{r:02x}{g:02x}{b:02x}'


# ═══════════════════════════════════════════════════════════════
#  APPLICATION
# ═══════════════════════════════════════════════════════════════

class App:
    """Full-featured simulator UI with dark theme and live controls."""

    def __init__(self, root):
        self.root = root
        self.root.title("Emergency Evacuation Simulator")
        self.root.configure(bg=C['bg'])
        self.root.resizable(False, False)

        # ── State ──
        self.maze = self.agent = self.path = None
        self.path_set = set()
        self.danger = {}
        self.running = False
        self.outcome = None          # 'success' | 'fire' | 'blocked'
        self.steps = 0
        self.t0 = 0
        self.phase = 0               # animation phase counter
        self.particles = []
        self.items = {}               # (r,c) → canvas rectangle id
        self.prev_fill = {}           # dirty-rect colour cache
        self.speed = 300              # ms per tick
        self.fire_p = 0.25            # fire spread probability

        # Agent draw position (floats for smooth interpolation)
        self.ax = self.ay = 0.0
        self.atx = self.aty = 0       # target pixel position

        self._build_ui()
        self._new_maze()
        self._idle_loop()             # ambient pulsing even when idle

    # ── UI Construction ───────────────────────────────────

    def _build_ui(self):
        # ── Title Bar ──
        top = tk.Frame(self.root, bg=C['panel'], padx=14, pady=8)
        top.pack(fill='x')
        tk.Label(top, text="🔥 EMERGENCY EVACUATION SIMULATOR",
                 font=("Consolas", 15, "bold"), fg=C['exit_on'],
                 bg=C['panel']).pack(side='left')
        self.lbl_status = tk.Label(top, text="READY",
                                   font=("Consolas", 11, "bold"),
                                   fg=C['ok'], bg=C['panel'])
        self.lbl_status.pack(side='right')

        # ── Main Area ──
        mid = tk.Frame(self.root, bg=C['bg'])
        mid.pack(fill='both', expand=True, padx=8, pady=4)

        self.canvas = tk.Canvas(
            mid, width=MAZE_COLS * CELL, height=MAZE_ROWS * CELL,
            bg=C['bg'], highlightthickness=2,
            highlightbackground=C['wall_hi'])
        self.canvas.pack(side='left', padx=(4, 8), pady=4)

        # ── Stats Panel ──
        sp = tk.Frame(mid, bg=C['panel'], padx=14, pady=14)
        sp.pack(side='right', fill='y', padx=4, pady=4)

        tk.Label(sp, text="━━━ STATISTICS ━━━",
                 font=("Consolas", 10, "bold"), fg=C['exit_on'],
                 bg=C['panel']).pack(anchor='w', pady=(0, 8))

        self.slbl = {}
        for key, icon in [('steps', '📍 Steps'),
                          ('time',  '⏱  Time'),
                          ('fire',  '🔥 Fire'),
                          ('path',  '🛤  Path'),
                          ('state', '⚡ State')]:
            row = tk.Frame(sp, bg=C['panel'])
            row.pack(fill='x', pady=2)
            tk.Label(row, text=icon, font=("Consolas", 9),
                     fg=C['dim'], bg=C['panel'], width=10,
                     anchor='w').pack(side='left')
            val = tk.Label(row, text="—", font=("Consolas", 9, "bold"),
                           fg=C['text'], bg=C['panel'], anchor='w')
            val.pack(side='left', padx=(4, 0))
            self.slbl[key] = val

        # ── Legend ──
        tk.Label(sp, text="\n━━━━ LEGEND ━━━━",
                 font=("Consolas", 10, "bold"), fg=C['exit_on'],
                 bg=C['panel']).pack(anchor='w', pady=(8, 4))
        for sym, txt, clr in [('●', 'Agent',  C['agent']),
                               ('■', 'Fire',   C['fire'][0]),
                               ('◆', 'Exit',   C['exit_on']),
                               ('▪', 'Path',   C['path']),
                               ('░', 'Danger', C['danger'][3])]:
            lf = tk.Frame(sp, bg=C['panel'])
            lf.pack(fill='x', pady=1)
            tk.Label(lf, text=f"  {sym}  {txt}", font=("Consolas", 9),
                     fg=clr, bg=C['panel']).pack(anchor='w')

        # ── Control Bar ──
        bot = tk.Frame(self.root, bg=C['panel'], padx=14, pady=8)
        bot.pack(fill='x', padx=8, pady=(0, 8))

        bs = dict(font=("Consolas", 10, "bold"), fg=C['btn_fg'],
                  bg=C['btn_bg'], activeforeground=C['bg'],
                  activebackground=C['btn_fg'], relief='flat',
                  padx=10, pady=4, cursor='hand2', bd=0)

        bf = tk.Frame(bot, bg=C['panel'])
        bf.pack(side='left')
        self.btn_go = tk.Button(bf, text="▶  START",
                                command=self._start, **bs)
        self.btn_go.pack(side='left', padx=(0, 6))
        tk.Button(bf, text="⟳  RESET",
                  command=self._reset, **bs).pack(side='left', padx=(0, 6))
        tk.Button(bf, text="🗺  NEW MAZE",
                  command=self._new_maze, **bs).pack(side='left')

        # Sliders
        sf = tk.Frame(bot, bg=C['panel'])
        sf.pack(side='right')
        for label, lo, hi, default, attr, div in [
            ("Speed", 50, 800, 300, 'speed', 1),
            ("Fire %", 5, 50, 25, 'fire_p', 100),
        ]:
            tk.Label(sf, text=label, font=("Consolas", 8),
                     fg=C['dim'], bg=C['panel']).pack(side='left', padx=(10, 2))
            var = tk.IntVar(value=default)

            def _cmd(v, a=attr, d=div):
                setattr(self, a, int(v) / d if d > 1 else int(v))

            tk.Scale(sf, from_=lo, to=hi, orient='horizontal',
                     variable=var, length=100, showvalue=False,
                     bg=C['panel'], fg=C['text'],
                     troughcolor=C['wall'], highlightthickness=0,
                     bd=0, sliderrelief='flat',
                     command=_cmd).pack(side='left')

    # ── Maze lifecycle ─────────────────────────────────────

    def _new_maze(self):
        self.running = False
        self.outcome = None
        grid = generate_maze(n_fires=random.randint(3, 7))
        self.maze = Maze(grid)
        self.agent = self.maze.start
        self.path = None
        self.path_set = set()
        self.danger = {}
        self.steps = 0
        self.particles = []
        self.prev_fill = {}
        if self.agent:
            self.ax = self.agent[1] * CELL + CELL / 2
            self.ay = self.agent[0] * CELL + CELL / 2
        self.lbl_status.config(text="READY", fg=C['ok'])
        self._refresh_stats()
        self._build_canvas()

    def _reset(self):
        self._new_maze()

    # ── Dirty-Rect Canvas ─────────────────────────────────

    def _build_canvas(self):
        """Create all cell rectangles once; later mutate via itemconfig."""
        self.canvas.delete('all')
        self.items.clear()
        self.prev_fill.clear()
        for r in range(self.maze.rows):
            for c in range(self.maze.cols):
                x1, y1 = c * CELL, r * CELL
                fill = self._cell_color(r, c)
                edge = C['wall_hi'] if self.maze.grid[r][c] == '#' else C['floor_edge']
                iid = self.canvas.create_rectangle(
                    x1, y1, x1 + CELL, y1 + CELL,
                    fill=fill, outline=edge, width=1)
                self.items[(r, c)] = iid
                self.prev_fill[(r, c)] = fill
        self._draw_agent()
        self._draw_exits()

    def _cell_color(self, r, c):
        """Return the fill colour for a cell based on current state."""
        p = (r, c)
        if p in self.maze.fires:
            return C['fire'][(self.phase + r + c) % 4]
        if self.maze.grid[r][c] == '#':
            # Subtle per-cell wall variation for depth
            v = 0x1c + ((r * 3 + c * 7) % 6)
            return f'#{v:02x}{v:02x}{v + 0x20:02x}'
        if p in self.maze.exits:
            return C['exit_on'] if self.phase % 3 else C['exit_off']
        if p in self.path_set:
            return C['path']
        # Danger-zone warm tint
        d = self.danger.get(p, 99)
        if d <= 2:
            return C['danger'][3]
        elif d <= 3:
            return C['danger'][2]
        elif d <= 5:
            return C['danger'][1]
        return C['floor']

    def _sync_cells(self):
        """Update only cells whose colour has changed (dirty-rect)."""
        for r in range(self.maze.rows):
            for c in range(self.maze.cols):
                f = self._cell_color(r, c)
                if f != self.prev_fill.get((r, c)):
                    self.canvas.itemconfig(self.items[(r, c)], fill=f)
                    self.prev_fill[(r, c)] = f

    # ── Visual Layers ─────────────────────────────────────

    def _draw_agent(self):
        self.canvas.delete('agent')
        if not self.agent:
            return
        x, y = self.ax, self.ay
        R = CELL // 2
        # Outer glow
        self.canvas.create_oval(
            x - R - 3, y - R - 3, x + R + 3, y + R + 3,
            fill=C['agent_glow'], outline='', tags='agent')
        # Body
        self.canvas.create_oval(
            x - R + 2, y - R + 2, x + R - 2, y + R - 2,
            fill=C['agent'], outline=C['agent_hi'], width=2, tags='agent')
        # Highlight dot
        hr = R // 2
        self.canvas.create_oval(
            x - hr, y - hr - 1, x + hr - 2, y - 1,
            fill=C['agent_hi'], outline='', tags='agent')

    def _draw_exits(self):
        self.canvas.delete('beacon')
        for r, c in self.maze.exits:
            x = c * CELL + CELL / 2
            y = r * CELL + CELL / 2
            pulse = 3 + 2 * math.sin(self.phase * 0.4)
            rr = CELL // 2 + int(pulse)
            self.canvas.create_oval(
                x - rr, y - rr, x + rr, y + rr,
                outline=C['exit_on'], width=2, tags='beacon')
        self.canvas.tag_raise('agent')

    def _draw_fire_glow(self):
        self.canvas.delete('fglow')
        for r, c in self.maze.fires:
            x = c * CELL + CELL / 2
            y = r * CELL + CELL / 2
            rr = CELL // 2 + 5
            self.canvas.create_oval(
                x - rr, y - rr, x + rr, y + rr,
                fill=C['fire_glow'], outline='', tags='fglow')
        self.canvas.tag_raise('beacon')
        self.canvas.tag_raise('agent')

    # ── Particle effects ──────────────────────────────────

    def _emit_sparks(self):
        """Spawn orange/red sparks from fire frontier cells."""
        src = list(self.maze.fire_frontier)
        for r, c in random.sample(src, min(3, len(src))):
            x = c * CELL + CELL / 2
            y = r * CELL + CELL / 2
            self.particles.append(Spark(
                x, y,
                random.uniform(-1.5, 1.5), random.uniform(-3.0, -0.5),
                random.randint(10, 22),
                random.choice(list(C['fire'])),
                random.randint(2, 4)))

    def _emit_celebration(self):
        """Burst of multi-colour confetti at agent position."""
        x, y = self.ax, self.ay
        palette = [C['agent'], C['exit_on'], C['path'], C['accent'], '#ffffff']
        for _ in range(50):
            self.particles.append(Spark(
                x, y,
                random.uniform(-5, 5), random.uniform(-7, -1),
                random.randint(18, 45),
                random.choice(palette),
                random.randint(3, 6)))

    def _tick_particles(self):
        self.canvas.delete('spark')
        alive = []
        for p in self.particles:
            if p.tick():
                alive.append(p)
                s = max(1, int(p.sz * p.life / p.ml))
                self.canvas.create_oval(
                    p.x - s, p.y - s, p.x + s, p.y + s,
                    fill=p.faded_color(), outline='', tags='spark')
        self.particles = alive

    # ── Stats Panel ────────────────────────────────────────

    def _refresh_stats(self):
        self.slbl['steps'].config(text=str(self.steps))
        if self.t0 and self.running:
            self.slbl['time'].config(text=f"{time.time() - self.t0:.1f}s")
        elif not self.t0:
            self.slbl['time'].config(text="0.0s")
        if self.maze:
            floors = sum(1 for r in range(self.maze.rows)
                         for c in range(self.maze.cols)
                         if self.maze.grid[r][c] != '#')
            pct = len(self.maze.fires) / max(1, floors) * 100
            self.slbl['fire'].config(text=f"{pct:.0f}%")
            if self.path:
                self.slbl['path'].config(text=f"{len(self.path)} cells", fg=C['ok'])
            else:
                self.slbl['path'].config(text="—", fg=C['text'])
        labels = {None: "Idle", 'success': "SAFE ✓",
                  'fire': "CAUGHT ✗", 'blocked': "STUCK ✗"}
        txt = "Running…" if self.running else labels.get(self.outcome, "Idle")
        fg = (C['ok'] if self.outcome == 'success'
              else C['fail'] if self.outcome in ('fire', 'blocked')
              else C['text'])
        self.slbl['state'].config(text=txt, fg=fg)

    # ── Simulation Control ─────────────────────────────────

    def _start(self):
        if not self.running and self.outcome is None:
            self.running = True
            self.t0 = time.time()
            self.lbl_status.config(text="SIMULATING", fg=C['accent'])
            self._sim_tick()

    def _sim_tick(self):
        if not self.running:
            return
        self.phase += 1

        # ── End conditions ──
        if self.agent in self.maze.exits:
            self.outcome = 'success'
            self.running = False
            self.lbl_status.config(text="✓ EVACUATED", fg=C['ok'])
            self._emit_celebration()
            self._render_final()
            return

        if self.agent in self.maze.fires:
            self.outcome = 'fire'
            self.running = False
            self.lbl_status.config(text="✗ CAUGHT IN FIRE", fg=C['fail'])
            self._render_final()
            return

        # ── Pathfind ──
        self.path = a_star(self.maze, self.agent)
        if not self.path:
            self.outcome = 'blocked'
            self.running = False
            self.lbl_status.config(text="✗ NO ESCAPE", fg=C['fail'])
            self._render_final()
            return
        self.path_set = set(self.path)

        # ── Move ──
        if len(self.path) > 1:
            self.agent = self.path[1]
            self.steps += 1

        # ── Fire ──
        self.maze.spread_fire(self.fire_p)
        self.danger = self.maze.danger_map()

        # ── Particles ──
        if self.maze.fire_frontier:
            self._emit_sparks()

        # ── Set animation target ──
        self.atx = self.agent[1] * CELL + CELL / 2
        self.aty = self.agent[0] * CELL + CELL / 2

        # ── Render cells, then smoothly glide agent ──
        self._sync_cells()
        self._draw_fire_glow()
        self._draw_exits()
        self._interp(INTERP_FRAMES)

    def _interp(self, remain):
        """Smooth ease-out glide of agent toward target cell."""
        if remain <= 0:
            self.ax, self.ay = float(self.atx), float(self.aty)
            self._draw_agent()
            self._tick_particles()
            self._refresh_stats()
            delay = max(30, self.speed - INTERP_FRAMES * INTERP_MS)
            self.root.after(delay, self._sim_tick)
            return
        self.ax += (self.atx - self.ax) * 0.35
        self.ay += (self.aty - self.ay) * 0.35
        self._draw_agent()
        self._tick_particles()
        self.root.after(INTERP_MS, lambda: self._interp(remain - 1))

    def _render_final(self):
        """Full render at simulation end."""
        self.danger = self.maze.danger_map()
        self._sync_cells()
        self._draw_fire_glow()
        self._draw_agent()
        self._draw_exits()
        self._tick_particles()
        self._refresh_stats()
        if self.particles:
            self._particle_fade()

    def _particle_fade(self):
        """Continue particle animation after sim ends."""
        self._tick_particles()
        if self.particles:
            self.root.after(40, self._particle_fade)

    # ── Idle ambient animation ─────────────────────────────

    def _idle_loop(self):
        """Pulse exits & animate fire colours even when not simulating."""
        if not self.running:
            self.phase += 1
            self._draw_exits()
            self._tick_particles()
            if self.maze and self.maze.fires:
                for r, c in self.maze.fires:
                    f = C['fire'][(self.phase + r + c) % 4]
                    if f != self.prev_fill.get((r, c)):
                        self.canvas.itemconfig(
                            self.items[(r, c)], fill=f)
                        self.prev_fill[(r, c)] = f
        self.root.after(120, self._idle_loop)


# ═══════════════════════════════════════════════════════════════
#  MAIN
# ═══════════════════════════════════════════════════════════════

if __name__ == '__main__':
    root = tk.Tk()
    App(root)
    root.mainloop()