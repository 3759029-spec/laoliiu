# -*- coding: utf-8 -*-
"""极光世界 · 助手 —— 安卓（Kivy）版入口

设计原则
--------
1. **协议层一行不改**：所有收发/解析都在 `jg_core.py`（= PC 版 极光助手.py）
   里的 `Client` 类，它本来就不碰 Tkinter，只通过两个队列跟界面说话：
       client.cmds.put((命令, 参数))   ← 界面 → 后台
       client.ev.get()                 ← 后台 → 界面
2. 手机版只做**单账号单角色**：填账号密码 → 登录 → 拿分区 → 选角色进世界。
   PC 版那套「录入档案 + 多角色会话 + 多开」在手机上屏太小，先不做。
3. 资源（技能图标 / 物品名.txt / 刷阵宝箱ID.txt）第一次启动时从安装目录
   复制到可写目录，之后都从可写目录读。

跑法（Windows 开发机）
    pip install kivy
    copy ..\\极光助手.py jg_core.py
    python main.py

出 APK
    见同目录 buildozer.spec 与仓库根 .github/workflows/android.yml
"""
import os
import queue
import sys
import time
import traceback

# ---------- 0. 先定可写目录，并让核心模块用它（必须在 import jg_core 之前）----
def _pick_data_dir():
    """安卓上 __file__ 在 APK 私有目录里、不可写；改用 App 给的私有目录。

    ANDROID_PRIVATE 由 python-for-android 注入（/data/data/<包名>/files）。
    PC 上退到用户主目录下的 .jiguang，方便开发时调试。
    """
    for k in ('ANDROID_PRIVATE', 'ANDROID_APP_PATH'):
        v = (os.environ.get(k) or '').strip()
        if v and os.path.isdir(v):
            return v
    home = os.path.expanduser('~')
    return os.path.join(home, '.jiguang')


DATA_DIR = _pick_data_dir()
try:
    os.makedirs(DATA_DIR, exist_ok=True)
except Exception:
    pass
os.environ['JG_APPDIR'] = DATA_DIR

_HERE = os.path.dirname(os.path.abspath(__file__))


def _sync_assets():
    """把随包资源复制到可写目录（只复制缺的，不覆盖）"""
    import shutil
    # 技能图标目录
    src_dir = os.path.join(_HERE, '技能图标')
    dst_dir = os.path.join(DATA_DIR, '技能图标')
    try:
        if os.path.isdir(src_dir):
            os.makedirs(dst_dir, exist_ok=True)
            for n in os.listdir(src_dir):
                d = os.path.join(dst_dir, n)
                if not os.path.exists(d):
                    shutil.copy2(os.path.join(src_dir, n), d)
    except Exception:
        pass
    # 两个数据表
    for n in ('物品名.txt', '刷阵宝箱ID.txt', '技能格子.json'):
        s = os.path.join(_HERE, n)
        d = os.path.join(DATA_DIR, n)
        try:
            if os.path.exists(s) and not os.path.exists(d):
                shutil.copy2(s, d)
        except Exception:
            pass


_sync_assets()

sys.path.insert(0, _HERE)
import jg_core as core              # noqa: E402  ← 协议层（= PC 版主程序）

from kivy.app import App                                   # noqa: E402
from kivy.clock import Clock                               # noqa: E402
from kivy.core.text import LabelBase                       # noqa: E402
from kivy.metrics import dp                                # noqa: E402
from kivy.uix.boxlayout import BoxLayout                   # noqa: E402
from kivy.uix.button import Button                         # noqa: E402
from kivy.uix.gridlayout import GridLayout                 # noqa: E402
from kivy.uix.label import Label                           # noqa: E402
from kivy.uix.popup import Popup                           # noqa: E402
from kivy.uix.scrollview import ScrollView                 # noqa: E402
from kivy.uix.slider import Slider                         # noqa: E402
from kivy.uix.spinner import Spinner                       # noqa: E402
from kivy.uix.textinput import TextInput                   # noqa: E402
from kivy.uix.togglebutton import ToggleButton              # noqa: E402

# ---------- 1. 中文字体（不注册的话全是方块）-------------------------------
_CN = 'CN'
_FONT_CANDIDATES = [
    # 安卓（系统自带 CJK 字体，按新到旧）
    '/system/fonts/NotoSansCJK-Regular.ttc',
    '/system/fonts/NotoSansSC-Regular.otf',
    '/system/fonts/DroidSansFallback.ttf',
    '/system/fonts/DroidSansChinese.ttf',
    # Windows 开发机（本机调试时别满屏方块）
    'C:/Windows/Fonts/msyh.ttc',
    'C:/Windows/Fonts/simhei.ttf',
    # 随包自带（可选：把字体丢进 android/ 就会被一起打包）
    os.path.join(_HERE, 'NotoSansSC-Regular.otf'),
]
for _p in _FONT_CANDIDATES:
    try:
        if os.path.exists(_p):
            LabelBase.register(name=_CN, fn_regular=_p)
            break
    except Exception:
        pass

BG = (0.11, 0.12, 0.13, 1)
PANEL = (0.17, 0.18, 0.20, 1)
FG = (0.88, 0.89, 0.90, 1)
MUT = (0.55, 0.57, 0.60, 1)
GREEN = (0.10, 0.62, 0.32, 1)
RED = (0.78, 0.20, 0.20, 1)
BLUE = (0.18, 0.42, 0.78, 1)
AMBER = (0.82, 0.52, 0.10, 1)


def lbl(text='', size=13, color=FG, **kw):
    kw.setdefault('font_name', _CN)
    return Label(text=text, font_size=dp(size), color=color, **kw)


def txt(hint='', password=False, **kw):
    kw.setdefault('font_name', _CN)
    return TextInput(hint_text=hint, password=password,
                     font_size=dp(14), multiline=False,
                     background_color=(0.22, 0.23, 0.25, 1),
                     foreground_color=FG, **kw)


def btn(text, cb=None, color=PANEL, size=13, **kw):
    kw.setdefault('font_name', _CN)
    b = Button(text=text, font_size=dp(size), background_normal='',
               background_color=color, **kw)
    if cb:
        b.bind(on_release=lambda *_: cb())
    return b


class Bar(BoxLayout):
    """一条带文字的进度条（血/蓝/经验共用）"""

    def __init__(self, title, color, **kw):
        super(Bar, self).__init__(orientation='vertical', size_hint_y=None,
                                  height=dp(38), spacing=dp(1), **kw)
        self.color = color
        self.lb = lbl('%s —' % title, 12, color)
        self.add_widget(self.lb)
        self.sub = lbl('', 9, MUT, size_hint_y=None, height=dp(2))
        self.add_widget(self.sub)

    def set(self, title, cur, mx):
        try:
            if not mx:
                self.lb.text = '%s —' % title
                self.sub.text = ''
                return
            cur = int(cur or 0)
            mx = int(mx)
            pct = max(0, min(100, int(cur * 100.0 / mx))) if mx else 0
            self.lb.text = '%s %d/%d  %d%%' % (title, cur, mx, pct)
            # 用字符块画进度条，避免依赖额外图形资源
            n = int(pct / 5)
            self.sub.text = '█' * n + '░' * (20 - n)
            self.sub.color = self.color
        except Exception:
            pass


class SlotBtn(Button):
    """一个技能格"""

    def __init__(self, idx, **kw):
        kw.setdefault('font_name', _CN)
        super(SlotBtn, self).__init__(font_size=dp(11),
                                      background_normal='',
                                      background_color=PANEL, **kw)
        self.idx = idx
        self.sid = 0
        self.sel = False

    def paint(self):
        self.background_color = GREEN if self.sel else PANEL


class Root(BoxLayout):

    def __init__(self, **kw):
        super(Root, self).__init__(orientation='vertical', padding=dp(6),
                                   spacing=dp(5), **kw)
        self.cl = core.Client(queue.Queue())
        self.cl.start()

        self.rows = []          # 档案（手机版只留本次登录那个）
        self.cur = None         # 当前角色 row
        self.lines = []         # 分区
        self.roles = []         # 角色
        self.learned = set()
        self.slots = []         # 6 个 SlotBtn
        self.auto_on = False
        self.busy = False
        self._logs = []

        self._build()

    # ---------------- 界面
    def _build(self):
        # —— 顶部：状态
        self.lb_state = lbl('未登录', 14, MUT)
        self.add_widget(self.lb_state)

        # —— 血 / 蓝 / 经验
        self.bar_hp = Bar('血', RED)
        self.bar_mp = Bar('蓝', BLUE)
        self.bar_exp = Bar('经验', AMBER)
        for b in (self.bar_hp, self.bar_mp, self.bar_exp):
            self.add_widget(b)

        # —— 账号区（登录后可折叠）
        self.box_login = BoxLayout(orientation='vertical', size_hint_y=None,
                                   height=dp(96), spacing=dp(4))
        r1 = BoxLayout(spacing=dp(4), size_hint_y=None, height=dp(34))
        self.e_acct = txt('账号')
        self.e_pwd = txt('密码', password=True)
        r1.add_widget(self.e_acct)
        r1.add_widget(self.e_pwd)
        self.box_login.add_widget(r1)
        r2 = BoxLayout(spacing=dp(4), size_hint_y=None, height=dp(34))
        self.sp_line = Spinner(text='分区：登录后选择', values=[], font_name=_CN,
                               font_size=dp(12))
        self.btn_login = btn('登录并进入', self.on_login, GREEN)
        r2.add_widget(self.sp_line)
        r2.add_widget(self.btn_login)
        self.box_login.add_widget(r2)
        self.add_widget(self.box_login)

        # —— 角色行
        r3 = BoxLayout(spacing=dp(4), size_hint_y=None, height=dp(34))
        self.sp_role = Spinner(text='角色：—', values=[], font_name=_CN,
                               font_size=dp(12))
        self.btn_online = btn('上线', self.on_enter, PANEL)
        self.btn_off = btn('下线', self.on_logout, PANEL)
        r3.add_widget(self.sp_role)
        r3.add_widget(self.btn_online)
        r3.add_widget(self.btn_off)
        self.add_widget(r3)

        # —— 技能格（3 列 × 2 行，跟 PC 版一致）
        g = GridLayout(cols=3, spacing=dp(4), size_hint_y=None, height=dp(120))
        for i in range(6):
            b = SlotBtn(i)
            b.bind(on_release=lambda w: self.on_slot(w))
            g.add_widget(b)
            self.slots.append(b)
        self.add_widget(g)

        # —— 开自动 / 开关
        r4 = BoxLayout(spacing=dp(4), size_hint_y=None, height=dp(34))
        self.btn_go = btn('开始打怪', self.on_go, GREEN)
        self.tg_team = ToggleButton(text='自动组队', font_name=_CN,
                                    font_size=dp(12), background_normal='',
                                    background_color=PANEL)
        self.tg_team.bind(on_release=lambda *_: self.on_team())
        self.tg_heal = ToggleButton(text='低血蓝凝神', font_name=_CN,
                                    font_size=dp(12), background_normal='',
                                    background_color=PANEL)
        self.tg_heal.bind(on_release=lambda *_: self.on_heal())
        r4.add_widget(self.btn_go)
        r4.add_widget(self.tg_team)
        r4.add_widget(self.tg_heal)
        self.add_widget(r4)

        r5 = BoxLayout(spacing=dp(4), size_hint_y=None, height=dp(30))
        r5.add_widget(lbl('阈值', 11, MUT, size_hint_x=None, width=dp(50)))
        self.sd_pct = Slider(min=10, max=90, step=5, value=30)
        self.lb_pct = lbl('30%', 12, FG, size_hint_x=None, width=dp(56))
        self.sd_pct.bind(value=lambda *a: self.on_pct())
        r5.add_widget(self.sd_pct)
        r5.add_widget(self.lb_pct)
        self.add_widget(r5)

        # —— 日志
        sv = ScrollView(do_scroll_x=False)
        self.lb_log = Label(text='', font_name=_CN, font_size=dp(10),
                            color=MUT, halign='left', valign='top',
                            size_hint_y=None, text_size=(dp(360), None))
        self.lb_log.bind(texture_size=lambda w, v: setattr(w, 'height',
                                                           v[1] or 10))
        sv.add_widget(self.lb_log)
        self.add_widget(sv)

        Clock.schedule_interval(self._pump, 0.2)

    # ---------------- 日志
    def log(self, s):
        t = time.strftime('%H:%M:%S')
        self._logs.append('[%s] %s' % (t, s))
        if len(self._logs) > 120:
            del self._logs[:-120]
        self.lb_log.text = '\n'.join(self._logs)

    def say(self, s):
        self.lb_state.text = s

    # ---------------- 登录
    def on_login(self):
        acct = (self.e_acct.text or '').strip()
        pwd = (self.e_pwd.text or '').strip()
        if not acct or not pwd:
            self.say('先填账号和密码')
            return
        if self.busy:
            return
        self.busy = True
        self.btn_login.text = '登录中…'
        self.lines = []
        self.sp_line.values = []
        self.sp_line.text = '分区：读取中…'
        self.log('[*] 登录账号「%s」…' % acct)
        self.cl.post('login', host=core.LOGIN_HOST_DEF,
                     port=core.LOGIN_PORT_DEF, acct=acct, pwd=pwd)

    def on_enter(self):
        """上线：没有分区就等；有分区就发 enter（它会自己读角色、选角、进世界）"""
        if not self.lines:
            self.say('请先登录（要在分区列表出来之后）')
            return
        line = self._line_by_name(self.sp_line.text)
        name = self._role_name()
        self.log('[*] 进入分区「%s」，角色「%s」…'
                 % ((line or {}).get('name') or '?', name or '默认第一个'))
        self.cl.post('enter', line=line, role_name=name or None)

    def on_logout(self):
        self.cl.post('logout')
        self.say('正在下线…')

    def _line_by_name(self, text):
        t = (text or '').split('：')[-1].strip()
        for ln in self.lines:
            if (ln.get('name') or '').strip() == t:
                return ln
        return self.lines[0] if self.lines else None

    def _role_name(self):
        t = (self.sp_role.text or '').split('：')[-1].strip()
        return '' if t in ('—', '') else t

    # ---------------- 打怪 / 技能格
    def on_slot(self, w):
        if not w.sid:
            self._pick_skill(w)
            return
        w.sel = not w.sel
        w.paint()
        self.log('   %s：%s' % ('选中' if w.sel else '取消',
                                (core.skill_cfg(w.sid) or {}).get('name')
                                or w.sid))
        self._push_auto_if_on()

    def _combo(self):
        out = []
        for w in self.slots:
            if w.sid and w.sel:
                _s, _stp, _grp = core.cast_profile(w.sid)
                out.append((w.sid, _grp, _stp))
        return out

    def _push_auto_if_on(self):
        if not self.auto_on:
            return
        cb = self._combo()
        if cb:
            self.cl.post('auto', on=True, combo=cb)
        else:
            self.auto_on = False
            self.btn_go.text = '开始打怪'
            self.cl.post('auto', on=False)

    def on_go(self):
        if not self.auto_on:
            cb = self._combo()
            if not cb:
                self.say('先点几个技能格选中（绿 = 参与连招）')
                return
            self.auto_on = True
            self.btn_go.text = '停止'
            self.btn_go.background_color = RED
            self.cl.post('auto', on=True, combo=cb)
            self.log('[*] 开始打怪：%d 个技能轮流' % len(cb))
        else:
            self.auto_on = False
            self.btn_go.text = '开始打怪'
            self.btn_go.background_color = GREEN
            self.cl.post('auto', on=False)
            self.log('[*] 已停止')

    def on_team(self):
        on = self.tg_team.state == 'down'
        self.tg_team.background_color = GREEN if on else PANEL
        self.cl.post('team', on=on)

    def on_heal(self):
        on = self.tg_heal.state == 'down'
        self.tg_heal.background_color = GREEN if on else PANEL
        self.cl.post('heal', on=on, pct=int(self.sd_pct.value))

    def on_pct(self):
        v = int(self.sd_pct.value)
        self.lb_pct.text = '%d%%' % v
        if self.tg_heal.state == 'down':
            self.cl.post('heal', on=True, pct=v)

    def _pick_skill(self, w):
        """点空格子 → 从已学技能里挑一个（手机上没有右键，用弹窗）"""
        ids = sorted(self.learned or ())
        if not ids:
            self.say('还没读到已学技能（要先上线）')
            return
        g = GridLayout(cols=2, spacing=dp(3), size_hint_y=None)
        g.bind(minimum_height=g.setter('height'))
        sv = ScrollView()
        sv.add_widget(g)
        pop = Popup(title='选技能', content=sv, size_hint=(0.9, 0.8))

        def choose(sid):
            w.sid = sid
            w.text = (core.skill_cfg(sid) or {}).get('name') or str(sid)
            w.sel = True
            w.paint()
            pop.dismiss()
            self._save_slots()
            self._push_auto_if_on()

        for sid in ids:
            nm = (core.skill_cfg(sid) or {}).get('name') or ('技能%d' % sid)
            g.add_widget(btn('%s' % nm, (lambda s=sid: choose(s)),
                             PANEL, 11, size_hint_y=None, height=dp(40)))
        pop.open()

    def _save_slots(self):
        """把 6 个格子存成 __default__（手机版不分角色，配置简单些）"""
        try:
            a = [w.sid for w in self.slots]
            core.save_slots(a, [], core.SLOT_DEFAULT_KEY)
        except Exception:
            pass

    def _load_slots(self):
        try:
            a, _b = core.load_slots(core.SLOT_DEFAULT_KEY)
        except Exception:
            a = []
        for i, w in enumerate(self.slots):
            sid = int(a[i]) if i < len(a) else 0
            w.sid = sid
            if sid:
                w.text = (core.skill_cfg(sid) or {}).get('name') or str(sid)
                w.sel = False          # 选中态不落盘，进来是未选
            w.paint()

    # ---------------- 事件泵
    def _pump(self, _dt):
        # 一次最多处理 60 条，别把 UI 卡住
        for _ in range(60):
            try:
                kind, data = self.cl.ev.get_nowait()
            except queue.Empty:
                break
            except Exception:
                break
            try:
                self._on_ev(kind, data)
            except Exception:
                self.log('[!] 界面处理 %s 出错：%s' % (kind, traceback.format_exc(0)))
        return True

    def _on_ev(self, kind, data):
        c = self.cl
        if kind == 'log':
            self.log(data if isinstance(data, str) else str(data))
        elif kind == 'state':
            self.say(str(data))
        elif kind in ('areas', 'lines'):
            if kind == 'lines':
                self.lines = list(data or [])
                names = ['分区：%s' % (ln.get('name') or '?') for ln in self.lines]
                self.sp_line.values = names
                if names:
                    self.sp_line.text = names[0]
                self.busy = False
                self.btn_login.text = '重新登录'
                self.log('[*] 读到 %d 个分区' % len(names))
        elif kind == 'roles':
            self.roles = list(data or [])
            names = ['角色：%s' % (r.get('name') or '?') for r in self.roles]
            self.sp_role.values = names
            if names:
                self.sp_role.text = names[0]
            self.log('[*] 读到 %d 个角色' % len(names))
        elif kind == 'online':
            self.say('已上线')
            self.btn_online.text = '换角色'
            self._load_slots()
        elif kind == 'offline':
            self.say('已下线')
            self.bar_hp.set('血', 0, 0)
            self.bar_mp.set('蓝', 0, 0)
        elif kind == 'error':
            self.busy = False
            self.btn_login.text = '登录并进入'
            self.say('出错：%s' % data)
        elif kind == 'self_hp':
            d = data or {}
            self.bar_hp.set('血', d.get('hp'), d.get('max'))
            self.bar_mp.set('蓝', d.get('mp'), d.get('mp_max'))
        elif kind == 'self_lv':
            d = data or {}
            lv = d.get('lv')
            e, n = d.get('exp'), d.get('need')
            self.bar_exp.set('Lv.%s 经验' % (lv or '?'), e, n)
        elif kind == 'learned':
            ids = set((data or {}).get('ids') or ())
            if ids:
                self.learned |= ids
                self.log('[*] 已学技能 %d 个' % len(self.learned))
        elif kind == 'wlines':
            self.log('[*] 线路：%s' % ('默认线路' if not data
                                      else '%d 条' % len(data)))
        elif kind == 'team_res':
            on = bool((data or {}).get('on'))
            self.tg_team.state = 'down' if on else 'normal'
            self.tg_team.background_color = GREEN if on else PANEL
        elif kind == 'heal_res':
            d = data or {}
            on = bool(d.get('on'))
            self.tg_heal.state = 'down' if on else 'normal'
            self.tg_heal.background_color = GREEN if on else PANEL
            if d.get('pct'):
                self.sd_pct.value = int(d['pct'])
        elif kind == 'auto_res':
            on = bool((data or {}).get('on'))
            self.auto_on = on
            self.btn_go.text = '停止' if on else '开始打怪'
            self.btn_go.background_color = RED if on else GREEN
        # 其它事件（npcs/bag_box/atk_res/skill_seen…）手机版第一版不展示

    def on_stop(self):
        try:
            self.cl.post('quit')
        except Exception:
            pass


class JiguangApp(App):
    title = '极光助手'

    def build(self):
        self.root_w = Root()
        return self.root_w

    def on_start(self):
        # 兜底：字体一个都没找到时提示一下（否则满屏方块）
        if not any(os.path.exists(p) for p in _FONT_CANDIDATES):
            self.root_w.log('[!] 没找到中文字体，界面可能显示方块')

    def on_pause(self):
        return True          # 后台不销毁（挂机时切出去还能活一会儿）

    def on_stop(self):
        try:
            self.root_w.on_stop()
        except Exception:
            pass


if __name__ == '__main__':
    JiguangApp().run()
