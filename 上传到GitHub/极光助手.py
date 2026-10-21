# -*- coding: utf-8 -*-
"""
极光世界 · 助手 v3
================================================================
界面按用户给定的三栏设计重做：

  ┌──────────┬──────────────┬──────────────┐
  │ 账号/登录 │              │  任务相关     │
  │ 大区信息  │   角色列表    │  （任务设置）  │
  │ 分区      │  （勾选表格）  │  （任务状态）  │
  │ 角色信息  │              │  （步骤表）    │
  │ 进入游戏  │              │              │
  ├──────────┴──────────────┴──────────────┤
  │  日志 …                批量进入 批量下线 退出程序 │
  └────────────────────────────────────────┘

功能（协议层与实测脚本 脱机进世界.py 完全一致，勿改）：
  ① 账号登录        0x126 → 0x111 → 0x113（取会话令牌）
  ② 大区/分区列表   0x121 大区｜0x117 分区(每分区一个 World 地址)
  ③ 读取角色        连 World → 0x207 → … → 0x205（每角色一帧）
  ④ 选择角色        0x205 选角 → 0x204 → 0x213 大世界线路表
  ⑤ 进入世界        0x20f → 0x214 → 0x401 + 0x43e → 0x6e2 → 0x4b0
  ⑥ 在线挂机        每秒 0x50f 心跳（时钟源 = 服务端 0x71d 时钟广播；3 秒无应答重发）
  ⑦ 下线            停心跳 + shutdown/close（立刻释放账号）

任务栏：仅界面（用户明确要求），开始/停止任务做了最简接线。
================================================================
"""
import os
import sys
import time
import uuid
import socket
import struct
import threading
import queue
import random
from fractions import Fraction          # 图标缩放凑整数倍用（Tk 只能整倍 zoom/subsample）

APP_VER = 'v6.2'
# v6.2 = ★★★ 修「自动凝神术勾了不灵敏、血蓝很少也不放」（用户反馈）
#        根因：检查原来只挂在属性变化（0x623/0x624）上 —— 站着不动、
#              或者「射程内没有怪」不打怪时根本没有属性包进来，于是长时间
#              一次都不检查。日志实证：小兰灯 21:47:42 → 21:48:24 空档 42 秒。
#        修法：① 主循环（本来就是 20Hz）加 _heal_tick()，每 0.3 秒评一次，
#                 不再依赖属性包；
#              ② 公共冷却（grp_cd）提前判掉，不白占节流时间；
#              ③ 节流 1.2s → 2.0s，并加 6 秒观察期：放完这 6 秒里血蓝在回升
#                 就不再施放（凝神术是持续回复，反复放等于一直重置它，
#                 表现就是「放了但血蓝不动」）；
#              ④ 血满只蓝低 / 蓝满只血低 都放（用户要求：哪个低都放）。
# v6.1 = ① ★ 修「切换角色后技能格绿框消失」：绿框（哪些格子参与连招）原来是
#            全局一份，load_slots_for() 里无条件 clear，一切角色就没了。
#            现在按角色记住（sel_memo），切回来绿框还在。
#        ② ★ 新增「血/蓝低于 X% 自动凝神术」：跟「自动同意组队」同一行，
#            勾选框 + 百分比下拉（10%~90%），血**或**蓝低于阈值就放凝神术。
#            技能 ID 认 10005（用户口报）/ 1005（客户端表里）/ 20019（旧ID），
#            优先用本角色 0x625 真学到的那个。带 1.2 秒节流 + 技能冷却保护，
#            死亡 / 未进世界 / 血蓝上限未知 一律不放。
# v6.0 = ★★★ 血/蓝/经验 全部按真机数值核准（场次 20261021_205740，
#         对照用户面板：血 853/1285、蓝 689/1017、经验 574626/938220）
#        ① **0x624 s_nSC_PlayerAttr**（98 字节，进世界下发一次）才是正源：
#             [0:4] cid | u16@38 当前血 | u16@42 当前蓝
#                       u16@50 血上限 | u16@54 蓝上限
#           以前等 0x623 的 2008/2009，而实测**根本不发** → 血条没分母、蓝条全空。
#        ② **0x60F 的经验/所需是 ×256 定点数**，必须右移 8 位：
#             147321856 >> 8 = 575476（= attr 3009 同值）
#             240184320 >> 8 = 938220（= 面板「升级所需」）
#           以前直接当整数用，所以经验显示成 1.47 亿。
#        ③ 变化量仍走 0x623：3001 当前血、3002 当前蓝（耗蓝时才发，本场 1 次）。
# v5.9 = ★★ 修「背包数量不更新」：
#        实测结论：用完物品后服务端只回一条 **17 字节差值包**
#        （`1b 01 1e00 13010000 00100000 00 ffffffff`），里面**没有数量字段**；
#        主动发 0x76 请求全量，服务端**根本不回**（20:44/20:48 两次日志实证）。
#        → 数量改成**本地自减**：使用成功后 bag[槽位] -= 1，归零则移除，
#          0.4 秒后推给界面；下次进世界/重读拿到 112 全量时自动校准。
#        另外 `do_bag_refresh` 不再 `bag.clear()`（服务端不回，清了就是永久丢）。
# v5.8 = ★ 诊断「蓝/等级/经验不读，只有血条准」+ 蓝条兜底：
#        ① `_note_self_attr` 里每个属性 ID **首次**出现时打一行
#           `[属性] 首次收到 attr 3001 = 12345`，一次上线就能看清服务端
#           到底推了哪些属性（血 3001/2008 有、蓝 3002/2009 有没有？）
#        ② attr 2009（法力上限）到达时也推一次 self_hp 事件 ——
#           有些角色只推上限不推当前值，以前这里不推事件，蓝条永远「—」
# v5.7 = ★ 修右栏被撑宽：Tk 的 Canvas 不给 width 时默认请求 378px，
#        pack(fill='x') 把这个请求宽度传给父容器 → 右栏（318 定死）被撑破、
#        血条还溢出到窗口外，中间角色列表被挤窄。给 Canvas 显式 width=180。
# v5.6 = ★ ① 角色信息区加三条进度条：血(红)/法力(蓝)/经验(金)，
#           数据仍走 0x623 attr 2008/2009 与 0x60F+0x623 5001/3009；
#           文字加深色描边（经验比例小时落在浅灰槽上要看得清）。
#        ② 修「使用后 6 个格子数量不更新」：用完后服务端只回 17 字节的
#           **差分** 0x613（`1b 01 槽位 ...`，跟 112 字节全量格式不同），
#           我们没解析它 → 数量一直是旧的。改成用完后 0.35 秒自动发 0x76
#           把整包背包重拉一次。
#        ③ _lv_show 兼容 need / expneed 两种键名。
# v5.5 = ★ 物品右键菜单：使用一次 / 用完为止（录制实证）
#        协议：0x411 s_nCS_PlayerItemOperation，子操作码 **0x07** = 使用物品。
#        24 字节载荷（场次 20261021_200949 / world_41002 / block 98 实录）：
#          07 01 | 槽位u16 | 05000000 | cid u32 | 8字节目标上下文 | 物品ID u32
#        发完服务端会回 0x60A（使用技能）+ 0x613（背包槽位数量更新）。
#        「用完为止」由 _tick 每秒发一次，数量归零自动停（上限 300 次保护）。
# v5.4 = ★ 图标缩放改法（用户：格子保持 48、不要 32、角标在图里面）：
#        Tk 只有整数倍 zoom/subsample，64→48 做不出来。改成 `_tk_resize_photo()`
#        纯 Tk 重采样（逐像素 get + 逐行 put，2304 次调用，实测每图标 3~4ms），
#        透明像素填 Canvas 底色。图标正好填满 48×48，数量角标自然压在图标
#        右下角内部。
# v5.3 = ★★★ 背包框按用户指定改造（2026-10-21 定案）：
#        ① 只显示 `刷阵宝箱ID.txt` 里列的物品，别的什么都不读
#           （不再按名字猜箱子、不再兜底铺前几件、不再有 is_box_item 筛选）。
#           该文件格式为 `ItemNameID<Tab>名字`，物品ID = ItemNameID - 100000，
#           两种 ID 都收，背包下发的是 ItemID。改文件不用重启，重新上线即生效。
#        ② 图标只读 `技能图标\` 里按名字命名的 png（神风分坛地灵宝箱.png 等），
#           名字对上就用，对不上白底写名字。删掉了 物品图标/ 那一整套缓存目录。
#        ③ 格子仍是 48×48；用户图标是 64×64，Tk 只能整数倍缩放，
#           所以按整数倍 subsample 到 ≤48（64→32），完整不裁边。
# v5.2 = ★★★ 图标对应不上的真根因（用户：「名字是对的图标对应不上」）：
#        物品图标根本不是从 Fashion9 / 某张表猜的，正确链路是
#          ItemID → 物品表 ItemDisplayID → GearDisplayInfo.txt 的 ICON
#                 → set:XXX image:YYY → icons_full/XXX/YYY.png
#        ⚠ 三个坑：① 要用 GearDisplayInfo.txt（25653 行），不是 ItemDisplayInfo.txt
#        （1733 行，只有装备）；② 任务物品/打造物品/心法各自是独立的
#        ItemID→DisplayID 表（QuestItemInfo/ItemCreateInfo/PsycheInfo），只查
#        item_info.csv 会漏掉一整批；③ Fashion9 是**时装头像**图集（64 张里
#        40 张还是空图），箱子从来不在里面。
#        已导出 物品图标/_items.json（8761 条）+ 1398 张 48x48 图标。
#        取图优先级：物品真实图标 → Fashion9 时装 → 通用宝箱 → 白底文字。
# v5.1 = ★ 箱子类物品现在有图标了：配置表里查不到专属图标的（夺宝宝箱 57202、
#        神风分坛地灵宝箱 22501…在 ItemDisplayInfo/GearInfo 里根本没行），
#        统一用 物品图标/_box.png（取自客户端 IcoItem_box 的银宝箱，预缩 48x48）。
# v5.0 = ★★ 修「刚才还能识别到神风教箱子，现在只剩白色 #222」的真因：
#        _bag_push 原来是「距上次推送不足 0.5 秒就直接 return 丢掉」，而 0x613
#        是几十帧连发的 → 只有第一帧推出去，后面全丢，之后没有新帧到来，
#        界面永远停在「只有第一件」。改成静默合并：收到帧只置 _bag_dirty，
#        由 _tick 在「距最后一帧 >=0.4 秒」时统一推一次完整的。
#        另外物品名表合并了 QuestItemName.txt（任务物品 2761 条）。
# v4.9 = ★ 背包不再按容器号硬拦（真机容器号可能跟录制不同，之前只进出 1 帧）；
#        前 8 帧打原始 hex；推送时容器 1 优先。
# v4.8 = ★ 背包加诊断 + 兜底：① 收到 0x613 打日志（首帧/每30帧，含槽位/
#        物品/数量），容器号不对也打出来；② 进世界 5 秒背包仍空 → 告警；
#        ③ 兜底：主背包有东西但一件箱子都没筛出来时，直接显示前 6 件，
#        免得界面空着让人以为没读到。
# v4.7 = ★ 修「v4.6 读不出背包」：load_items_for 原本无条件清空格子，
#        而 apply_cur 会在点角色/状态刷新时反复调用，跑在 bag_box 事件之后就
#        把刚填好的格子抹掉（0x613 只推一次，抹了就永远空）。改成从会话缓存的
#        s['boxes'] 恢复；另外进世界后 1.5 秒补发一次 0x411 主动要背包。
# v4.6 = ★ ① 物品格：读到物品就**不画背包背景**（底图会盖住素材/名字），
#           空格子才铺背景；数量改成黑底白字角标。
#        ② 修 NameError：_pump_sess 里 skill_seen 分支引用了从未定义的 SKLIB。
# v4.5 = ★ 物品格改成「自动识别背包里的箱子」：解析 0x613 PlayerItemOperation，
#        从主背包(容器1)里筛出名字含箱/匣/礼盒/锦囊 或 属于 Fashion9 的物品，
#        自动铺进 6 个 48x48 格子并显示数量（去掉手动点选）。
# v4.3 = ★ 角色信息区改版：删掉原来 9 行文字，只留「上线/编辑/删除」三个按钮；
#        新增 6 个「指定物品」格子（3 列 × 2 行，跟技能格同款）；
#        新增等级/经验显示（0x60F PlayerExpUpdate + 0x623 attr 5001/3009）。
#        ⚠ 物品格的背包读取逻辑按用户要求留到下一步。
# v4.2 = ★ 新增「自动接受队长召唤」：0x734 s_nSC_TeamLeaderCallMember → 回
#        0x4CD s_nCS_TeamMemberAcceptCall。⚠ 载荷结构尚未实证（17 场历史录制
#        里没出现过 0x734），先按「与组队邀请同构」发 pl[:8]，同时把 0x734
#        完整 hex 写进日志 —— 一次真实召唤就能定死。
# v4.1 = ★ 新增「自动同意组队」：收到服务端 0x684（别人邀请你入队）/
#        0x685（别人申请加入你的队）/ 0x686（队伍合并确认）时，自动回对应的
#        Ret 包，实现挂机时也能被拉进队伍。协议依据是录制 20261021_142646 与
#        20261021_144134 两场的实证（结构见 handle_frame 里那段注释）。
# v3.3 = 按真抓包把握手魔数改成 f6f30d04。★ 已回退，见下。
# v3.4 = ① 录入改成多线程（每次登录一条独立连接 + Client._login_gate 统一排队）
#        ② ★★★ 握手魔数**不是固定值**（13:05 实锤，最关键的发现）：
#           登录服 0x113 应答的 @4..7 是**每个账号专属**的 4 字节魔数 ——
#             gk623513 → f3f30d04
#             gk656929 → f7f30d04
#           0x207 / 0x201 / 0x202 / 0x205 / 0x401 全都要用服务端给的这个值
#           （Client.magic，do_login 时从 0x113 读）。
#           以前写死 f3f30d04，只有恰好拿到 f3 的账号能进 World，其余账号
#           握手直接 0x20C flag=1 被拒 —— 这就是"只有一个号能读到角色"的真相。
#           （v3.3 那次"按抓包改成 f6"同理：那个号当时拿到的就是 f6。）
#           ⚠ 以后别再写死任何魔数，也别再"按抓包"改。
#        ③ 录入连接不再"用完就断"，改成闲置池 PARK 复用（服务端对同账号的
#           World 会话释放极慢，断了重连必被晾着）。
# v3.5 = ★ 服务端限流防护（12:45 实测）：
#          连续失败后原来的代码会自动 3 秒重试，把本机 IP 直接送进服务端限流，
#          最后连登录服都回 WinError 10054。现在：
#            ① 登录 / 读角色 / 进世界 **全部取消自动重试**，失败就停，让用户手动决定
#            ② 界面加「失败刹车」net_guard()：5 分钟内失败 3 次就硬拦，不许再发连接
#            ③ 登录间隔 1.2s → 6s，同账号冷却 3s → 30s
LOGIN_HOST_DEF, LOGIN_PORT_DEF = '221.228.205.8', 20021
XOR_KEY = 0x07
# ★ 2026-10-21 多线程：每条客户端线程各连各的账号，所以「上次 World 断开时刻」
#   必须放在模块级。
# ★★★ 2026-10-21 修正：必须是**按账号**存的字典，不能是一个全局时间戳。
#   以前是一个 float，任何一条连接关 World 都写它、任何账号开 World 都读它 ——
#   多开挂机时随便哪个角色掉线，正在录入的另一个账号就白等 5 秒，
#   开得越多录入越卡（"多账号录入有问题"的直接原因之一）。
_WORLD_CLOSE_BY_ACCT = {}            # 账号 -> 上次断开 World 的时刻

# ★★★ 2026-10-21 多线程录入：每次点「登录」都新起一条独立 Client 线程。
#   但服务端会把「短时间内连续新建连接」判成异常连接直接拒（旧注释里实测
#   "一个都登不上"就是没节流）。所以这里做一个**全局登录闸门**：
#   所有线程排队领号，相邻两次真正开始连接至少隔 _LOGIN_MIN_GAP 秒。
#   这是"多线程录入"能成立的前提，别去掉。
_LOGIN_GATE = threading.Lock()
_LOGIN_LAST_T = [0.0]                # 上一次真正开始连接登录服的时刻
_LOGIN_MIN_GAP = 2.0                 # 相邻两次新建登录连接的最小间隔（秒）
                                     # 只防手滑连点，不是"限流"，别调太大
_LOGIN_T_BY_ACCT = {}                # 账号 -> 上次登录时刻（同账号冷却用）
_ACCT_COOLDOWN = 5.0                 # 同一账号重复登录要等的秒数
HB_BASE = 0x25fa017a                 # 兜底心跳基数（0x71d / 0x798 都拿不到时才用）

# ================================================================ 站桩自动打怪
# ---- ① 进入场景序列 ----
#   真客户端收到 0x603（自身数据）后 0.5 秒内必发这一串。
#   不发 → 服务端不认为角色进了 AOI → 之后所有世界交互（技能 / 自动战斗）都不被受理。
#   时序与载荷取自 脱机进世界.py 的实测实现（同样的包、同样的相对时刻）。
WTIME_FALLBACK = 0x05F5E2D8          # 0x41d 的世界时间字段（探不到真值时兜底）
SCENE_SPAM_47E = 26                  # 进场景后连续空查次数（真客户端 0.5 秒内发 40+ 次）

# ---- ② 服务端自带自动战斗 0x4C7 = s_nCS_FightBOTCmd（仅 1 字节）----
#   01 = 开启（以主玩家当前位置为活动中心）｜00 = 关闭｜02 = 续期（源码 +600 秒）
BOT_ON, BOT_OFF, BOT_RENEW = b'\x01', b'\x00', b'\x02'
BOT_RENEW_SEC = 480.0                # 续期间隔，比服务端 600 秒留 120 秒余量

# ---- ③ 实体 ID 值域（0x647 清单 / 0x62B 坐标 / 0x623 血量 共用）----
EID_NPC_LO, EID_NPC_HI = 0x02600000, 0x02800000
EID_TC_LO, EID_TC_HI = 0x04C40000, 0x04C70000

# ---- ④ 怪 / NPC 分类 ----
# 0x647 的 39 字节记录里只有「名字」，没有类型字段（结构：xyz + eid + 3 字节标志 + GBK 名字）。
# 所以判定只能靠名字查表。表来自 npc_location_with_names.xlsx 的「怪物NPC全量表」，
# 该表「类别」列只有 '怪物' / '任务NPC' 两种取值，已由 build_npc_class.py 导出成本地模块。
try:
    from npc_class import MONSTERS as _MON_LIST  # noqa: E402
    from npc_class import NPCS as _NPC_LIST
    from npc_class import AMBIG as _AMB_LIST
except Exception as _e:  # 模块缺失也不影响其他功能，只是分不出怪
    _MON_LIST, _NPC_LIST, _AMB_LIST = [], [], []
    print('[!] npc_class 未加载（%s）—— 无法区分怪与 NPC' % _e)

MON_SET = set(_MON_LIST)
NPC_SET = set(_NPC_LIST)
AMB_SET = set(_AMB_LIST)

# ---- ⑤ MNID 表：0x6B9 只给 MNID，靠这张表翻名字/等级/称号/类别 ----
#   数据来自 单机服/data/npc_master.tsv（13718 条，真录制验证命中率 165/165）
NPC_DB = {}
try:
    import npc_db as _npcdb
    NPC_DB = _npcdb.load()
except Exception as _e2:
    print('[!] npc_db 未加载（%s）—— 0x6B9 只能显示 MNID，翻不出名字' % _e2)

COORD_SCALE = 12.5                   # 0x6D3/0x6D4 的 u16 坐标 ÷ 12.5 = 世界坐标
                                     # 实测：z=1837 → 147.0，正好是城内地面高度
# ---- 0x6B9 里的定点坐标：world = (u16 - 8) / 16，整圈后会回到 0 ----
#      实测（用 0x647 里 15 个已知精确坐标的实体对表，误差 0.00 米）：
#        X 在 +0x09，周期 4096 米（u16 整 16 位）
#        Y 在 +0x0B，周期  512 米（只用低 13 位 → 8192/16）
#      ⚠ 之前 Y 老是差 512 米，就是把它当成 4096 周期了。
COORD_MOD_X = 4096.0
COORD_MOD_Y = 512.0


def fix16(u, near, period):
    """0x6B9 的定点坐标 → 世界坐标（用自己位置 near 反推该补几圈）

    只能在「离自己不到半圈」时可逆：X 半圈 2048 米、Y 半圈 256 米，
    AOI 范围（几十米）远小于这个，所以实战里不会歧义。
    """
    v = (u - 8) / 16.0
    return v + period * round((near - v) / period)

RADIUS = 50.0                        # 默认检测半径（米），界面上可改
ENT_TTL = 600.0                      # 台账里实体的兜底存活时间（秒）
                                     # ⚠ 不能设小：站桩不动的怪永远收不到坐标更新

# ★ 2026-10-20「怪物实时刷新」：服务端只在 AOI 握手（0x47E）后推一次完整实体清单
#   0x647，之后**新刷出来的怪不一定主动推** —— 站桩久了周围怪打光了就一直空着。
#   所以要像真客户端那样隔一会儿重新申报一次视野，把新刷的怪拉进来。
AOI_REFRESH_SEC = 8.0                # 轻刷新间隔：重发视野/AOI，不清台账
AOI_HARD_SEC = 25.0                  # 开着自动打怪却这么久找不到目标 → 重拉整张清单
SKIP_FAIL_N = 3                      # 同一只怪连续几次服务端没反应 → 暂时跳过
SKIP_FAIL_SEC = 30.0                 # 跳过多久后解禁


def mnid_info(mnid):
    """MNID -> (名字, 等级文本, 称号, 类型)；查不到返回 None"""
    r = NPC_DB.get(mnid)
    if not r:
        return None
    name, lv1, lv2, title, is_npc = r
    lv = '%d' % lv1 if lv1 == lv2 else '%d-%d' % (lv1, lv2)
    return (name, lv, '' if title in ('', 'null') else title,
            'NPC' if is_npc else '怪')


def npc_kind(name):
    """按名字判类型：怪 / NPC / 待定 / 未知"""
    n = (name or '').strip()
    if not n:
        return '未知'
    if n in MON_SET:
        return '怪'
    if n in NPC_SET:
        return 'NPC'
    if n in AMB_SET:
        return '待定'
    return '未知'

# ================================================================ 攻击（0x408）
# 载荷固定 36 字节 = 9 个 u32：
#   [0] 角色ID  [1] 技能ID  [2] 0  [3] 0  [4] 技能组  [5] step
#   [6] 目标ID  [7] 0  [8] 1
#
# ★★ 2026-10-20 用真客户端录制（同一角色打「七星魔女」）逐条对出来的：
#   c2s 0x408 共 10 条，全部 36 字节，形如
#     58060000 eb030000 00000000 00000000 1f000000 06000000 f8836202 00000000 01000000
#     角色=1624  技能=1003  组=31  step=6  目标=40010744   [7]=0  [8]=1
#   → [4]=技能配置里的 SchoolRep，[5]=CRRejectU（1003 正好 31 / 6）
#   → 服务端每次回 0x648 受理，CD 1500ms
#   以前发 7042 / 组 0 / step 0 —— 技能表里根本没这个 ID，服务端当然不理。
ATTACK_MIN_GAP = 0.25                # 两次攻击最小间隔（秒），防手抖连点
DEFAULT_RANGE_M = 15.0               # 配置表没写射程时用这个（= 冲击 1003 的 15 米）
PROBE_WAIT = 0.7                     # 探测技能时，每发一个等多久才算「没受理」
                                     #   真客户端攻击后 0.03s 服务端就回 0x60a，0.7 秒足够
PROBE_GAP = 0.8                      # 探测时两发之间的间隔

# ★★★ 「试一遍」的节奏 —— 2026-10-20 实测教训：
#   以前 SWEEP_WAIT=0.9 / GAP≈0，结果第一个技能 1005 成功后服务端下发
#   `0x648 整组CD初始化 1500ms`，后面 14 个全撞在公共CD里被静默丢弃，
#   测出来「17 个只有 3 个能用」全是假的。
#   现在每发之间至少隔 2.5 秒，稳稳跨过 1500ms 公共CD。
SWEEP_WAIT = 1.2                     # 发出去后等多久看有没有 0x60A
SWEEP_GAP = 2.5                      # 两发之间的总间隔（> 公共CD 1500ms）

# 服务端回过 0x648（受理）的技能 —— 才算「这个 ID 真能用」
# 同名技能有好几个等级 ID（伤痛咒 2001~2039），只有一个/几个是学会的，
# 光看配置表分不出来，只能让服务端告诉我们。
VERIFIED = set()
# 探测确认「服务端不认」的技能 ID —— 这些直接从下拉里去掉，不再显示
#   （同名技能有十几个等级，只有学会的那几个能用；没用的看得人头大）
HIDDEN = set()

# ★★★ 2026-10-20 定案：角色**真正学会**的技能 ID（服务端 0x625 s_nSC_InitPlayerSkill 下发）
#   这就是「技能列表全是重复、放了没反应」的总根因：
#     · 以前把 480 条技能全表灌进下拉 → 同一个技能十几级各占一行，用户找不到
#     · 发出去的 ID 角色根本没学 → 服务端静默丢弃，0x648/0x60A 一条都不回
#   真录制（角色 1835）0x625 只有 1 帧，正好 17 个：
#     1003 冲击 / 1002 / 1005 / 7002 伤痛咒 / 7043 / 7062 风寒蛊 / 7101 / 7121 /
#     7161 / 7201 / 7261 / 7321 / 7361 / 7401 / 7461 / 20006 回城 / 20071
#   → 下拉只显示这 17 个，绝不显示没学的。
LEARNED = set()          # 角色已学技能（0x625 下发）
LEARNED_CID = 0          # 这份列表属于哪个角色

# ★ 0x625 一次会带多个「等级形态」的同一个技能（1003 出现两次），
#   按名字去重后展示，避免看起来重复。
def _sk_name(sid):
    v = SKILL_DB.get(sid) if isinstance(SKILL_DB, dict) else None
    return (v or {}).get('name') or ''


def _state_path():
    return os.path.join(_APPDIR, '技能状态.json')


def load_state():
    """读回上次探测的成果：哪些技能能用、哪些不能用（学会状态不会变，存着省事）"""
    try:
        import json
        with open(_state_path(), encoding='utf-8') as f:
            d = json.load(f)
        for x in d.get('verified') or []:
            VERIFIED.add(int(x))
        for x in d.get('hidden') or []:
            HIDDEN.add(int(x))
    except Exception:
        pass


def save_state():
    try:
        import json
        tmp = _state_path() + '.tmp'
        with open(tmp, 'w', encoding='utf-8') as f:
            json.dump({'verified': sorted(VERIFIED),
                       'hidden': sorted(HIDDEN - VERIFIED)}, f)
        os.replace(tmp, _state_path())
    except Exception:
        pass


# ---- 怪物排除名单（2026-10-20 用户要求：怪名旁的小方框点一下出 X = 不打它）----
#   按**名字**排除（不是实体ID）：刷新出来的是新实体ID，但名字一样，照样排除。
def _bl_path():
    return os.path.join(_APPDIR, '怪物黑名单.json')


def load_blacklist():
    try:
        import json
        with open(_bl_path(), encoding='utf-8') as f:
            d = json.load(f)
        return set(str(x).strip() for x in (d.get('names') or []) if str(x).strip())
    except Exception:
        return set()


def save_blacklist(names):
    try:
        import json
        tmp = _bl_path() + '.tmp'
        with open(tmp, 'w', encoding='utf-8') as f:
            json.dump({'names': sorted(set(str(x).strip() for x in names
                                           if str(x).strip()))},
                      f, ensure_ascii=False)
        os.replace(tmp, _bl_path())
    except Exception:
        pass


ATTACK_ARG7 = 0                      # [7] 真包是 0/1，取多数值 0
ATTACK_TAIL = 1                      # [8] 真包恒为 1（回城包是别的值，攻击用 1）

# ---- 技能库 ----
# ★ 2026-10-20：以前这里的技能ID是从「极光流苏」C# 源码里抠的（7042 / 60003 …），
#   拿游戏自己的配置表一对，**大半根本不存在**，所以 0x408 发出去服务端一律不理。
#   现在改成从 `skill_db.py` 读（由 build_skill_db.py 从
#   Skill/SkillCreateInfo2.txt + StringManager/SkillName.txt 生成）。
#
# ★★ 0x408 的 [4] / [5] 两个字段就是配置表里的 SchoolRep / CRRejectU，不用猜：
#   技能 1003「冲击」→ SchoolRep=31 / CRRejectU=6，
#   真录制（同一角色打七星魔女）客户端发的正是 31 / 6，
#   服务端回 0x648 受理、CD 1500ms。这是唯一被实锤过的攻击技能。
try:
    import skill_db as _skdb
    SKILL_DB = _skdb.load()
except Exception as _e_sk:
    SKILL_DB = {}
    print('[!] skill_db 未加载（%s）—— 技能下拉只有内置两个', _e_sk)

# ★★★★ 2026-10-20 第五次修正：默认技能改成 **1003 法术攻击**
#   用户原话：「普通攻击和法术攻击是两个不同的技能」「你跟我把那个法术攻击加上去」
#   1003 = SkillName[201003] = 法术攻击，射程 15m / 吟唱 0.8s / HavetoEquip=0
#   为什么它比 7002 伤痛咒更适合当默认：
#     · 7002 是巫士门派技，别的职业根本没有，而且 HavetoEquip=1
#     · 1003 是**所有角色都有的基础法术攻击**，不依赖装备/门派
#   历史错误：以前默认 7002，注释写「抓包里客户端真发过」——
#     发过不代表能一直放，且它 SkillTarget=0（[6] 填自己），根本不打怪。
DEFAULT_SKILL = 1003                 # 法术攻击（基础攻击，人人都有）

# ★★★ 0x408 的 [4] 组 / [5] step —— 2026-10-20 用 **41 帧真包**定案（最终版，别再改）
#
#   载荷结构（36 字节 = 9 个 u32）：
#     [0] 角色ID  [1] 技能ID  [2] 0  [3] 0
#     [4] 组     [5] step   [6] 目标ID  [7] 0  [8] 1
#
#   ★★★ step 跟「目标是不是自己」走（2026-10-20 18:05 录制 20261020_180502，
#       角色 1835，29 帧；加历史 12 帧，共 41 帧零例外）：
#         目标 = 自己（自我施法）→ step = 5，组 = 391
#         目标 = 怪物（攻击/debuff）→ step = 6，组 = 392
#       实证：1005/7043/7161/7461/7321/20006 全部 自己+step5；
#             1003/1002/7062/7101/7121/7401/7361/7002 全部 怪+step6。
#       **这就是「门派技能放不出来」的根因**：以前自我施法类也按
#       step=6 + 目标=最近的怪发出去，服务端静默丢弃（连 0x648 都不回）。
#
#   ⚠ 组值服务端校验很松：31 / 24 / 391 / 392 都被接受过（同一个 1003
#     在三场录制里用过三个组值全活）。按上面真值走最稳，但组不是根因。
#   ⚠ 历史错误（都别再犯，这个字段已经被翻来覆去改错 5 次）：
#     × 「组/step 是全场常量 392/6」—— 只对攻击成立，自我施法是 391/5
#     × 用 SkillGroup(2002/2003/2042) 当 [4] → 服务端认不出
#     × 用 SchoolRep(31)/CRRejectU(6) 当 [4]/[5] → 语义完全无关
#     × 「组 = SkillNameID - 1000」→ 表里对得上，真包从没发过
DEFAULT_STEP = 6                      # 攻击类（目标=怪）
DEFAULT_GROUP = 392                   # 攻击类组值
SELF_STEP = 5                         # 自我施法类（目标=自己）
SELF_GROUP = 391                      # 自我施法类组值


def group_of(sid):
    """技能 → 发包用的 [4] 组值（攻击类默认 392）。

    ★ 2026-10-20 18:05 补充：组值**不是**技能属性也不是全场唯一常量，
      服务端对它的校验很松（31/24/391/392 都收）。自我施法类走 391
      （见 cast_profile），攻击类走配置表/392。
    """
    cfg = SKILL_DB.get(int(sid)) or {}
    g = cfg.get('group') or 0
    return g or DEFAULT_GROUP


# ★ 自我施法技能：目标必须填自己、step=5、组=391，且不发 0x43D。
#   2026-10-20 真客户端逐个点出来实证的（录制 20261020_180502）。
SELFCAST = {1005, 7043, 7161, 7461, 7321, 20006, 20019, 1004}
#   1005 凝神术 / 7043 调元 / 7161 惊天动地 / 7461 血祭 / 7321 野兽之魂
#   20006 回城 / 20019 凝神术(旧ID) / 1004 凝神
#   ⚠ 7002 伤痛咒、7361 聚元 虽然配置里 SkillTarget=0，真客户端是**当怪放**
#     （目标=怪、step=6），不在这个集合里 —— 加进来反而把能放的弄坏。


def cast_profile(sid):
    """技能 -> (是否自我施法, step, 组)。发包前一律先过这个函数。

    自我施法：目标填自己、step=5、组=391（真客户端实测）
    攻击/debuff：目标填怪、step=6、组=392（真客户端实测）
    """
    try:
        sid = int(sid)
    except (TypeError, ValueError):
        return False, DEFAULT_STEP, DEFAULT_GROUP
    if sid in SELFCAST:
        return True, SELF_STEP, SELF_GROUP
    return False, DEFAULT_STEP, group_of(sid) or DEFAULT_GROUP


# ================================================================ 冷却 / 消耗 / 前置
# ---- ① 冷却（0x648 的 [3] CD 毫秒）----
#   真客户端 recast 得比服务端声明早 0.1~0.8 秒（客户端冷却轮从施法起始就转，
#   服务端从受理才开始算），所以本地护栏统一减 1 秒，别比真客户端还严。
CD_GRACE = 1.0
#   例外：血祭 7461 服务端声明 60s，但真录制里 37.4 秒就 recast 且被受理
#   （那个 60s 是效果持续，不是冷却）。按观测值放，别硬等 60 秒。
OBSERVED_CD = {7461: 35.0}
#   其它长 CD 技能（惊天动地 120s 等）没有观测数据，先按「声明值 − 宽限」走，
#   界面上会把剩余时间显示出来，用户能自己判断要不要等。

# ---- ② 前置状态（配置表 C_BuffReqU 全 0，查不到，只能手工维护）----
#   技能 -> (依赖技能ID, 人话)。机制：依赖技能放成功后视为「在线」，
#   死亡清空。别的职业照着加即可。
PREREQ = {
    7201: (7321, '野兽之魂'),        # 牺牲：得先把野兽之魂召出来
}
SUMMON_TTL = 600.0                   # 前置状态保质期（秒），超时视为已消失


def cd_guard_sec(sid, stated_ms):
    """服务端声明的 CD(ms) -> 本地护栏秒数（比真客户端略松，别当过期的紧箍咒）"""
    sid = int(sid or 0)
    if sid in OBSERVED_CD:
        return OBSERVED_CD[sid]
    return max(0.3, (stated_ms or 0) / 1000.0 - CD_GRACE)


def prereq_of(sid):
    """技能的前置依赖 -> (依赖技能ID, 人话) 或 None"""
    return PREREQ.get(int(sid or 0))

DEFAULT_CLASS = SKILL_DB.get(DEFAULT_SKILL, {}).get('cls', 7)

# 内置备份：DB 没加载时至少这两个能用（回城 20006 是唯一实测过的真包）
SKILL_SEED = [
    # ★ 默认就是「法术攻击」1003 —— 用户要的那个基础攻击：
    #   射程 15m、吟唱 0.8s、需装备=0、不依赖任何门派技能书。
    (1003, SKILL_DB.get(1003, {}).get('name', '法术攻击'),
     SKILL_DB.get(1003, {}).get('group', 392),
     SKILL_DB.get(1003, {}).get('step', 6)),
    (20006, '回城', 391, 5),
]


def skill_block(sid):
    """技能属于哪个分支段（ID 千位）。Skillstudy 里 5 个职业各占一段：

    0~499 段 剑系（剑舞/剑影/割伤…）
    5000 段  法术系（乱剑术/冰封/冰雪…）
    6000 段  道系（冲击/三花聚顶/固本培元…）
    7000 段  巫系（伤痛咒/风寒蛊/噬心蛊…）  ← 2026-10-20 抓包确认是「巫士」的
    8000 段  灭魔咒（3 个）
    只要不是同一段，基本就不是同一个职业的技能。
    """
    try:
        sid = int(sid)
    except (TypeError, ValueError):
        return -1
    return 0 if sid < 1000 else sid // 1000 * 1000


# ★ 通用技能：所有职业都能用，切换分支时也一直显示在列表里
#   ★★★★ 2026-10-20 第四次修正（用户当场指出「普通攻击和法术攻击是两个不同的技能」）
#   ------------------------------------------------------------
#   以前这里写的是 3001，而且名字标成「普通攻击」—— 两处都错：
#     · SkillName[203001] = 「打开礼包」，根本不是攻击技能
#     · 3001 打出去服务端不会当普攻处理
#   查 SkillName.txt 的 201xxx / 202xxx 段（= 0x408 的 [1]）得到的真名：
#     1101 = 普通攻击(物理)     1102 = 普通攻击(法术)
#     1001 = 攻击               1002 = 重劈
#     1003 = **法术攻击**（射程 15m / 吟唱 0.8s / 需装备=0）  ← 用户要的「基础法术攻击」
#     1004 = 凝神               1005 = 凝神术
#   旁证：服务端 0x60A 广播里确实出现过 1101 —— 说明它就是服务端认的普攻形态。
#   ⚠ HavetoEquip 只提示不拦截（录制实证 7002 需装备仍能放），所以 1101/1102 照发。
COMMON_SKILLS = (1101, 1102, 1003, 1002, 1001, 1004, 1005, 20006, 20019)
#   1101 普通攻击(物理)  1102 普通攻击(法术)  —— 两个「基础攻击」
#   1003 法术攻击        1002 重劈            —— 基础法术/物理伤害技
#   1001 攻击            1004 凝神   1005 凝神术
#   20006 回城           20019 凝神术（旧ID，保留兼容）


# 段号 → 界面标签（用该段前几个技能名当代表）
def _build_block_choices():
    pool = {}
    for sid, v in SKILL_DB.items():
        if sid in COMMON_SKILLS:
            continue                       # 通用技能常驻，不占分支
        pool.setdefault(skill_block(sid), []).append((sid, v['name']))
    out = [('全部', -1)]
    for blk in sorted(pool):
        rows = sorted(pool[blk])
        uniq = []
        for _, n in rows:
            if n not in uniq:
                uniq.append(n)
        span = ('1~499' if blk == 0 else str(blk))
        tag = '（巫士）' if blk == 7000 else ''
        out.append(('%s 段%s：%s（%d）'
                    % (span, tag, '/'.join(uniq[:2]), len(rows)), blk))
    out.append(('通用：普通攻击/法术攻击/回城（%d）' % len(COMMON_SKILLS), -2))
    return out


BLOCK_CHOICES = _build_block_choices()


def skill_cfg(sid):
    """技能ID → 配置（名字/射程/吟唱/group/step）；查不到返回 None"""
    try:
        return SKILL_DB.get(int(sid))
    except (TypeError, ValueError):
        return None


def mk_cfg(sid):
    """技能ID → 能直接发包用的一份配置，**永远不返回 None**

    ★ 2026-10-20 新增：像 7321 野兽之魂 / 7402 战意 / 20071 这些，
    在 Skillstudy 和 SkillCreateInfo2 里都查不到完整行，
    skill_cfg() 会返回 None（或全是 0），发包时就退回全局默认值 ——
    又是老毛病。这里统一兜一层：组值按 NameID-1000 推，step 用 6。
    """
    c = dict(skill_cfg(sid) or {})
    c['id'] = int(sid)
    c.setdefault('name', '')
    _sc, _stp, _grp = cast_profile(sid)
    c['group'] = c.get('group') or _grp
    c['step'] = c.get('step') or _stp
    c['rng'] = c.get('rng') or 0
    c['cast'] = c.get('cast') or 0
    c['nosel'] = bool(c.get('nosel'))
    c['equip'] = bool(c.get('equip'))
    return c


def skill_values(kw='', extra=None, blk=-1, learned=None):
    """技能下拉的全部选项：'ID · 名字 (射程)'；给了 kw 就按子串过滤

    ★★★ 2026-10-20 重写：只列「角色真学会的」技能。
    以前是把 SKILL_DB 全表 480 条灌进下拉 —— 同一个技能十几级、几百行长得一样，
    用户原话「大量重复」，而且里面绝大多数角色根本没学，发出去服务端不理。
    现在以 0x625 s_nSC_InitPlayerSkill 下发的「已学技能」为唯一白名单：
      · 已学非空 → 只显示这几个（外加通用 3 个兜底）
      · 已学为空（还没连/服务端没发）→ 才退回全表，并标一行提示

    ★ 2026-10-21 多开：learned 由调用方传（当前选中角色的 client.learned），
      不再读模块级 LEARNED —— 否则两个角色同时在线会互相覆盖。
    """
    LRN = set(learned or ())
    pool = {}
    for sid, v in SKILL_DB.items():
        pool[sid] = v
    for sid, nm, g, st in SKILL_SEED:
        pool.setdefault(sid, {'name': nm, 'cls': 0, 'school': g, 'cr': st,
                              'rng': 0, 'cast': 0})
    for k, v in (extra or {}).items():
        try:
            # ⚠ 老版本把查不到名字的技能写成 '服务端收录' 存进了 技能库.json，
            #   于是下拉里出现「7003 · 服务端收录」（它其实是伤痛咒）。
            #   这里把这种占位名当空的处理，让下面退化成「技能<ID>」。
            _nm = (v.get('name') or '').strip()
            if _nm in ('服务端收录', '服务端收录的', ''):
                _nm = ''
            pool.setdefault(int(k), {'name': _nm, 'cls': 0,
                                     'school': v.get('group', 0),
                                     'cr': v.get('step', 0),
                                     'rng': 0, 'cast': 0})
            if _nm and int(k) not in SKILL_DB:
                pool[int(k)]['name'] = _nm     # 配置表没有的，用自定义名字
        except (TypeError, ValueError):
            continue
    # ★ 白名单：学会了才允许出现
    allow = set(LRN) | set(COMMON_SKILLS) if LRN else set(pool)
    # ★ 已学但配置表里查不到的 ID（1002 / 1005 / 20071…）：也要列出来，
    #   否则用户会发现「服务端说学了 17 个，下拉里只有 13 个」。名字用 ID 顶。
    if LRN:
        for sid in LRN:
            pool.setdefault(sid, {'name': '技能%d' % sid, 'cls': 0,
                                  'school': 0, 'cr': 0, 'rng': 0, 'cast': 0})
    # ★ 2026-10-20 19:xx 修「凝神术重复」：COMMON_SKILLS 里的旧 ID
    #   （20019 凝神术）和已学的真身（1005 凝神术）同名，下拉出现两行。
    #   口径：**已学技能的名字占用后，COMMON 里的同名旧 ID 不再显示**
    #   （1101/1102/1003 这些没有已学同名的，照常显示）。
    _learned_names = set()
    for sid in (LRN or ()):
        _n = ((SKILL_DB.get(sid) or {}).get('name')
              or (pool.get(sid) or {}).get('name') or '').strip()
        if _n:
            _learned_names.add(_n)
    out, seen = [], set()
    for sid in sorted(pool):
        if sid not in allow:
            continue                        # 没学的，一个都不显示
        v = pool[sid]
        nm = (v.get('name') or '').strip()
        # COMMON 里的旧 ID 撞了已学技能的名 → 跳过（20019 凝神术这类）
        if (sid not in LRN and sid in COMMON_SKILLS
                and nm and nm in _learned_names):
            continue
        # ★ 同名多级的去重：只留第一个 ID
        #   ⚠ 2026-10-20 修：以前这里是 `if key in seen and sid not in LEARNED`，
        #   于是 1002/1005 冲击（服务端明确说学了）被 1003 挤掉了；
        #   反过来 7001/7002/7003 三个学了的同名技能又会重复显示三行。
        #   现在的口径：**学了的全部保留**（它们各自是不同 ID，服务端认哪个就是哪个），
        #   只有「没学的同名技能」才去重。
        key = nm or ('#%d' % sid)
        if key in seen and sid not in LRN:
            continue
        seen.add(key)
        mark = '✓ ' if sid in VERIFIED else ''
        disp = nm or ('技能%d' % sid)        # 名字查不到就只显示 ID，别编假名
        if v.get('rng'):
            txt = '%s%d · %s (%gm)' % (mark, sid, disp, v['rng'] / 100.0)
        else:
            txt = '%s%d · %s' % (mark, sid, disp)
        # ★ 2026-10-20 19:3x 「需装备」标记已取消（用户要求）。
        #   理由是真客户端抓包实证：7002 伤痛咒 HavetoEquip=1，服务端照样回
        #   5 次 0x60A 确认施法；风寒蛊/巫毒印/噬魂蛊等一堆 equip=1 的技能
        #   也全部施放成功。HavetoEquip 只影响客户端界面上技能亮不亮，
        #   **服务端根本不校验装备**。挂着这个标记只会误导用户以为技能有限制。
        #   ⚠ 历史教训：我曾拿它当拦截门槛，把 7xxx 全拦了，是错的，已拆除。
        #   ★ 「自我施法」= 目标填自己、step=5、组=391（真客户端实证）
        if sid in SELFCAST:
            txt += ' [自我施法]'
        if v.get('nosel'):
            txt += ' [无需目标]'
        # ★ 前置依赖（牺牲←野兽之魂这类），配置表 C_BuffReqU 全 0 查不到，
        #   靠 PREREQ 表手工维护（别的职业照着加）
        _pq = prereq_of(sid)
        if _pq:
            txt += ' [需:%s]' % _pq[1]
        if sid in HIDDEN and sid not in VERIFIED:
            continue                        # 探测确认不能用 → 不显示
        if blk == -2:                       # 只想看通用技能
            if sid not in COMMON_SKILLS:
                continue
        elif (blk >= 0 and skill_block(sid) != blk
              and sid not in COMMON_SKILLS):   # 通用技能常驻，不受分支影响
            continue
        if kw and kw not in txt:
            continue
        out.append(txt)
    return out


def _skill_path():
    # _APPDIR 在本段后面才定义，所以延迟取
    return os.path.join(_APPDIR, '技能库.json')


def load_skills():
    """技能库：DB 里的全部真实技能 + 用户保存的自定义覆盖

    返回 {技能ID字符串: {name, group, step}}
    group/step 默认取配置表的 SchoolRep / CRRejectU（已实证就是 0x408 的 [4]/[5]）。
    """
    d = {}
    for sid, v in SKILL_DB.items():
        d[str(sid)] = {'name': v['name'], 'group': v['group'],
                       'step': v['step']}
    for sid, nm, g, st in SKILL_SEED:
        d.setdefault(str(sid), {'name': nm, 'group': g, 'step': st})
    try:
        import json
        with open(_skill_path(), encoding='utf-8') as f:
            for k, v in json.load(f).items():
                # 只接受用户在配置文件里显式改过的值，别把 DB 的正确值覆盖掉
                cur = d.get(str(int(k)), {})
                _g = int(v.get('group') or 0)
                _st = int(v.get('step') or 0)
                d[str(int(k))] = {
                    'name': v.get('name') or cur.get('name') or '技能%s' % k,
                    # 0 视为「没填」，别把配置表里正确的 group/step 冲成 0
                    'group': _g if _g else cur.get('group', 0),
                    'step': _st if _st else cur.get('step', 0)}
    except Exception:
        pass
    return d


def save_skills(d):
    try:
        import json
        p = _skill_path()
        tmp = p + '.tmp'
        with open(tmp, 'w', encoding='utf-8') as f:
            json.dump(d, f, ensure_ascii=False, indent=1)
        os.replace(tmp, p)
    except Exception:
        pass


# ★ 2026-10-21 补：`_pump_sess` 里处理 skill_seen 事件时引用了 `SKLIB`，但这个
#   名字**从来没定义过** —— 平时不触发，一旦服务端确认了一个库里没有的新技能就
#   抛 NameError（界面日志里就是「[!] 贝利亚 刷新出错：name 'SKLIB' is not defined」）。
#   这里补一个带缓存的取用入口；注意 load_skills() 的键是**字符串**。
_SKLIB = {'d': None}


def skill_lib():
    """技能库（懒加载 + 缓存），键是字符串 ID"""
    if _SKLIB['d'] is None:
        _SKLIB['d'] = load_skills()
    return _SKLIB['d']


# ================================================================ 技能格子（2026-10-20 新版界面）
# 布局（用户手绘框架）：6 个攻击格 + 「开始」+ 2 个通用格。
#   · 空框点击 = 添加技能（弹列表选）；添加后固定在该格，存 exe 同级 技能格子.json
#   · 打怪时点中某个攻击格 = 选中，点「开始」用它自动打
#   · 通用格添加后自动释放（冷却好了就放，受 _cast_block 的蓝/血/前置保护）
#   · 格中技能冷却中 → 图标变黑白 + 角上显示剩余秒数
#   · 图标：把真客户端抓的技能图标按 <技能ID>.png 放进 exe 同级 技能图标/ 即可，
#     没有图标就显示文字（名字+ID），抓到图标后自动切换，不用改代码
N_ATK_SLOT, N_BUF_SLOT = 6, 2


def _slots_path():
    return os.path.join(_APPDIR, '技能格子.json')


# ★★★ 2026-10-21：技能格绑定改成**按角色分开存**。
#   以前是一份全局的（技能格子.json 顶层就 atk/buf），多角色一上就串：
#   给巫士配好的 6 个攻击技，切到别的角色还照着放。
#   新格式 {"version":2,"roles":{"<角色键>":{atk:[...],buf:[...]}}}
#   旧文件（顶层 atk/buf）读的时候自动当成 "__default__" 那一份，不丢配置。
SLOT_DEFAULT_KEY = '__default__'


def _slots_all():
    """整份技能格文件 -> {角色键: {'atk':..,'buf':..}}"""
    try:
        import json
        with open(_slots_path(), encoding='utf-8') as f:
            d = json.load(f)
    except Exception:
        return {}
    if isinstance(d, dict) and isinstance(d.get('roles'), dict):
        out = {}
        for k, v in d['roles'].items():
            if isinstance(v, dict):
                out[str(k)] = v
        return out
    if isinstance(d, dict) and ('atk' in d or 'buf' in d):   # 旧格式
        return {SLOT_DEFAULT_KEY: d}
    return {}


def load_slots(key=None):
    """读回某个角色的技能格绑定 -> (atk[6], buf[2])；没有就全空

    key=None 时退回 "__default__"（还没录入任何角色时的默认一套）。
    """
    k = str(key) if key else SLOT_DEFAULT_KEY
    all_sl = _slots_all()
    d = all_sl.get(k)
    if d is None and SLOT_DEFAULT_KEY in all_sl:
        # 老版本只有一份全局配置（存在于 __default__）：新录入的角色先继承它，
        # 免得升级后所有角色的技能格都是空的、要重新配一遍。
        d = all_sl.get(SLOT_DEFAULT_KEY)
    d = d or {}
    try:
        a = [int(x or 0) for x in (d.get('atk') or [])][:N_ATK_SLOT]
        b = [int(x or 0) for x in (d.get('buf') or [])][:N_BUF_SLOT]
    except Exception:
        a, b = [], []
    while len(a) < N_ATK_SLOT:
        a.append(0)
    while len(b) < N_BUF_SLOT:
        b.append(0)
    return a, b


def save_slots(atk, buf, key=None):
    """只覆盖该角色那一份，别的角色原样保留"""
    try:
        import json
        k = str(key) if key else SLOT_DEFAULT_KEY
        all_sl = _slots_all()
        all_sl[k] = {'atk': [int(x or 0) for x in atk][:N_ATK_SLOT],
                     'buf': [int(x or 0) for x in buf][:N_BUF_SLOT]}
        tmp = _slots_path() + '.tmp'
        with open(tmp, 'w', encoding='utf-8') as f:
            json.dump({'version': 2, 'roles': all_sl}, f,
                      ensure_ascii=False, indent=1)
        os.replace(tmp, _slots_path())
    except Exception:
        pass


# ================================================================ 背包物品格
# ★ 2026-10-21 新增（用户要求）：角色信息区原来的 9 行文字去掉，换成 6 个
#   「指定物品」格子（3 列 × 2 行，样式跟技能格一致），用来盯背包里某几样
#   东西还剩多少 —— 挂机时最常看的就是药水/材料。
#
#   配置存 exe 同级 物品格子.json，同样**按角色分开**：
#     {"version": 2, "roles": {"<角色键>": {"items": [id1..id6]}}}
#   0 表示空格子。
N_ITEM_SLOT = 6


class _NullLabel(object):
    """「界面已经删掉、但旧代码还在 configure」的标签桩。

    ★ 2026-10-21：角色信息区那 9 行文字在界面上被删掉了，但 apply_cur /
      hp_mp_text / root._jg 等一堆地方还在 lbl.configure(...)。用这个桩接住
      所有调用，既不用去翻改上百行旧代码，也不会因为拿不到控件而崩。
    """

    def configure(self, *a, **k):
        pass

    config = configure

    def __getattr__(self, n):
        return lambda *a, **k: None


def _items_path():
    return os.path.join(_APPDIR, '物品格子.json')


# ---- 物品名表 ----------------------------------------------------------
# ★ 2026-10-21：物品 ID 有了，界面上得显示名字。名字在客户端的
#   configs_decrypted/StringManager/ItemName.txt（TSV：ItemNameID \t 名字，
#   **GBK 编码**，ItemNameID = ItemID + 100000）。
#   这个文件不能打进 exe（游戏更新就过期），所以运行时按顺序找：
#     1) exe 同级/物品名.txt        —— 用户自己放的，优先级最高
#     2) exe 同级/物品名.json       —— {"10007": "主城回城符", ...}
#     3) 不找游戏目录（换台电脑就没有了），找不到就显示 #ID
_ITEM_NAME = {'db': None, 'path': None}


def _load_item_names():
    """懒加载物品名表 -> dict{int: str}；加载失败返回 {}"""
    if _ITEM_NAME['db'] is not None:
        return _ITEM_NAME['db']
    db = {}
    import json as _json
    _bases = [_APPDIR]
    _mp = getattr(sys, '_MEIPASS', None)
    if _mp:
        _bases.append(_mp)          # 打包进 exe 的那份（和技能图标同一套逻辑）
    p1 = None
    for _b in _bases:
        for _n in ('物品名.json', '物品名.txt'):
            _p = os.path.join(_b, _n)
            if os.path.exists(_p):
                p1 = _p
                break
        if p1:
            break
    if p1 and p1.endswith('.json'):
        try:
            with open(p1, encoding='utf-8') as f:
                for k, v in _json.load(f).items():
                    db[int(k)] = str(v)
            _ITEM_NAME['path'] = p1
        except Exception:
            db = {}
    if not db and p1 and p1.endswith('.txt'):
        try:
            with open(p1, 'rb') as f:
                raw = f.read()
            try:
                txt = raw.decode('gbk')
            except Exception:
                txt = raw.decode('utf-8', 'ignore')
            for line in txt.splitlines():
                parts = line.rstrip('\r').split('\t')
                if len(parts) < 2 or not parts[0].strip().isdigit():
                    continue
                nid = int(parts[0])
                if nid >= 100000:          # ItemNameID -> ItemID
                    db[nid - 100000] = parts[1].strip()
            _ITEM_NAME['path'] = p1
        except Exception:
            db = {}
    _ITEM_NAME['db'] = db
    return db


def item_name(iid):
    """物品 ID -> 名字；表里没有返回 ''（界面自己回落到 #ID）"""
    try:
        return _load_item_names().get(int(iid), '')
    except Exception:
        return ''


# ---- 时装图标（Fashion9）------------------------------------------------
# ★ 2026-10-21：用户要求物品格「只读取 icons_full/Fashion9 里的那些箱子」，
#   并且他**不知道这些图标对应哪个物品 ID**。所以这里把官方配置表的链路打通：
#
#     Fashion9/FASH9_XX.png
#       ← GearDisplayInfo.txt 的 ICON 列（ItemDisplayID → "set:Fashion9 image:FASH9_XX"）
#       ← GearInfo.txt 的 ItemDisplayID → ItemID / ItemNameID
#       ← ItemName.txt 的 ItemNameID → 名字（时装这批在名字表里是缺的，会回落图标名）
#
#   结果预先导成 时装图标/_索引.json：{"FASH9_01": {"display": 81107, "items": [...]}}
#   ⚠ 一个图标可能对应多个 ItemID（男/女款、不同品阶），所以 items 是数组。
_FASH9 = {'idx': None, 'rev': None}


def _fash9_dir():
    """时装图标目录：exe 同级「时装图标」优先，再 exe 内部（和技能图标同一套逻辑）"""
    for base in (_APPDIR, getattr(sys, '_MEIPASS', None)):
        if not base:
            continue
        p = os.path.join(base, '时装图标')
        if os.path.isdir(p):
            return p
    return None


def fash9_index():
    """FASH9_XX -> {'display': 显示ID, 'items': [{'item','name',...}]}"""
    if _FASH9['idx'] is not None:
        return _FASH9['idx']
    import json as _json          # ★ 模块顶部没 import json，这里必须局部导入
    d = {}
    p = _fash9_dir()
    if p:
        fp = os.path.join(p, '_索引.json')
        try:
            with open(fp, encoding='utf-8') as f:
                d = _json.load(f)
        except Exception as ex:
            # ⚠ 别静默吞：这里读不出来，选择器就是空的，必须让人看见原因
            print('[!] 读时装索引失败 %s：%s' % (fp, ex))
            d = {}
    _FASH9['idx'] = d
    return d


def fash9_icon_of(item_id):
    """物品 ID -> Fashion9 图标名（FASH9_XX）；不是时装就返回 ''"""
    iid = int(item_id or 0)
    if not iid:
        return ''
    if _FASH9['rev'] is None:
        rev = {}
        for k, v in fash9_index().items():
            for it in (v.get('items') or []):
                try:
                    rev.setdefault(int(it.get('item') or 0), k)
                except Exception:
                    pass
        _FASH9['rev'] = rev
    return _FASH9['rev'].get(iid, '')


_ICON_CACHE = {}


def _item_icon_dir():
    """物品图标目录（exe 同级「物品图标」优先，再 exe 内部）"""
    for base in (_APPDIR, getattr(sys, '_MEIPASS', None)):
        if not base:
            continue
        p = os.path.join(base, '物品图标')
        if os.path.isdir(p):
            return p
    return None


_BOX_PHOTO = {'img': None, 'tried': False}


def box_photo():
    """通用宝箱图标 —— 箱子类物品在配置表里查不到专属图标时用这个

    ★ 2026-10-21：用户「箱子图标出不来」。查下来原因是这些箱子（夺宝宝箱 57202、
      神风分坛地灵宝箱 22501…）在 `ItemDisplayInfo.txt` / `GearInfo.txt` 里
      **根本没有行**，拿不到 ICON 字段，所以只能退化成文字。
      真客户端那套图标资源在 `D:\\极光世界\\icons_full\\IcoItem_box\\`
      （64 个袋子/宝箱），这里取 Item_Box_22（银宝箱）预缩成 48x48，
      放在 exe 同级 `物品图标/_box.png`，所有认不出的箱子共用它。
    """
    if _BOX_PHOTO['tried']:
        return _BOX_PHOTO['img']
    _BOX_PHOTO['tried'] = True
    import tkinter as tk            # 同 fash9_photo：本文件 tk 是函数内局部 import
    d = _item_icon_dir()
    if not d:
        return None
    p = os.path.join(d, '_box.png')
    if not os.path.exists(p):
        return None
    try:
        _BOX_PHOTO['img'] = tk.PhotoImage(file=p)
    except Exception as ex:
        print('[!] 宝箱图标加载失败 %s：%s' % (p, ex))
    return _BOX_PHOTO['img']



# 箱子判定关键词（用户要「自动识别背包里的箱子」）
_BOX_KW = ('箱', '匣', '礼盒', '锦囊', '包裹', '宝袋', '锦盒')


def is_box_item(iid):
    """这个物品算不算「箱子」

    ★ 2026-10-21：判定两条路，满足其一就算 ——
      ① 名字里带 箱 / 匣 / 礼盒 / 锦囊 / 包裹 …（真·箱子、宝箱）
      ② 属于 Fashion9（用户点名要盯的就是这一批，图标在 时装图标/ 里）
    名字查不到（ItemName.txt 只覆盖到 10026 号物品）时靠 ② 兜底。
    """
    iid = int(iid or 0)
    if not iid:
        return False
    if fash9_icon_of(iid):
        return True
    nm = item_name(iid)
    return bool(nm) and any(k in nm for k in _BOX_KW)



# ================================================================ 真实物品图标
# ★★★ 2026-10-21 定案：物品图标到底怎么取（这次是完整链路，别再猜）
#
#   ItemID
#     → 物品表 ItemDisplayID   （Item/**/GearInfo|QuestItemInfo|ItemCreateInfo|PsycheInfo，
#                               导出汇总在 item_info.csv）
#     → GearDisplayInfo.txt 的 ICON 列：`set:ItemIcon3 image:ItemIcon3_25`
#     → D:\极光世界\icons_full\ItemIcon3\ItemIcon3_25.png
#
#   ⚠ 三处坑：
#   1. 不是 ItemDisplayInfo.txt（那张只有 1733 行，是装备显示，普通物品查不到）；
#      必须用 **GearDisplayInfo.txt**（25653 行，覆盖全部 DisplayID）。
#   2. 任务物品（QuestItemInfo.txt）、打造物品（ItemCreateInfo.txt）、
#      心法（PsycheInfo.txt）是**各自独立的 ItemID→DisplayID 表**，
#      只查 item_info.csv 会漏掉一批（神风教系列就在任务物品表里）。
#   3. set 名里有一批（Others / Enchant / Portion1 / Portion2 / Collection1）
#      在 icons_full 里**没有拆出单图**，这些物品取不到图标，回落到通用宝箱/文字。
#
#   已导出：`物品图标/_items.json` = {ItemID: "Set__Image"}（8761 条）
#            `物品图标/<Set>__<Image>.png`（1398 张，预缩 48x48，PIL 预先缩好，
#            因为 Tk 只支持整数倍 zoom/subsample，不能运行时缩放）
_ITEMS_IDX = {'map': None}
_ITEM_PHOTO_CACHE = {}


def _items_index():
    """ItemID -> 'Set__Image'；读 物品图标/_items.json"""
    if _ITEMS_IDX['map'] is not None:
        return _ITEMS_IDX['map']
    import json as _json
    d = {}
    p = _item_icon_dir()
    if p:
        fp = os.path.join(p, '_items.json')
        try:
            with open(fp, encoding='utf-8') as f:
                d = _json.load(f)
        except Exception as ex:
            print('[!] 读物品图标索引失败 %s：%s' % (fp, ex))
            d = {}
    _ITEMS_IDX['map'] = d
    return d


def item_photo(item_id):
    """物品 ID -> tk.PhotoImage（48x48），没有对应图标返回 None"""
    iid = int(item_id or 0)
    if not iid:
        return None
    if iid in _ITEM_PHOTO_CACHE:
        return _ITEM_PHOTO_CACHE[iid]
    key = _items_index().get(str(iid)) or _items_index().get(iid)
    if not key:
        _ITEM_PHOTO_CACHE[iid] = None
        return None
    d = _item_icon_dir()
    if not d:
        return None
    p = os.path.join(d, key + '.png')
    if not os.path.exists(p):
        _ITEM_PHOTO_CACHE[iid] = None
        return None
    try:
        import tkinter as tk        # 同 fash9_photo：模块级没有 tk
        img = tk.PhotoImage(file=p)
    except Exception as ex:
        print('[!] 物品图标加载失败 %s：%s' % (p, ex))
        _ITEM_PHOTO_CACHE[iid] = None
        return None
    _ITEM_PHOTO_CACHE[iid] = img     # 必须留引用，否则被 GC 掉变空白
    return img


# ================================================================ 刷阵宝箱（用户指定）
# ★★★ 2026-10-21 用户明确要求：背包框**只显示他指定的宝箱**，图标用
#   `技能图标\` 里那批按**名字**命名的 png（如「神风分坛地灵宝箱.png」）。
#
#   两件事：
#   1. 筛选：`刷阵宝箱ID.txt`（每行一个物品ID，也支持逗号/空格分隔）非空时
#      **只认这些 ID**；文件为空时退回「名字能在图标目录里找到」。
#   2. 图标：`物品图标\box48\<名字>.png`（构建期用 PIL 把 技能图标 里那批
#      64x64 预缩成 48x48 —— Tk 只能整数倍缩放，不能运行时缩），
#      找不到再直接读 `技能图标\<名字>.png`（64x64，会略溢出格子但能看）。
_BOX_ICONS = {'map': None}


def _box_icon_map():
    """宝箱名字 -> 图标文件路径；**只读 `技能图标\\`**（用户指定）

    ★ 2026-10-21 用户定案：图标就用他自己放进 `技能图标\\` 的那批 png，
      文件名 = 物品名（`神风分坛地灵宝箱.png`）。不要任何导出/缓存目录。
    """
    if _BOX_ICONS['map'] is not None:
        return _BOX_ICONS['map']
    d = {}
    for base in (_APPDIR, getattr(sys, '_MEIPASS', None)):
        if not base:
            continue
        p = os.path.join(base, '技能图标')
        if not os.path.isdir(p):
            continue
        for f in os.listdir(p):
            if f.lower().endswith('.png') and '宝箱' in f:
                d.setdefault(f[:-4], os.path.join(p, f))
    _BOX_ICONS['map'] = d
    return d


def _tk_resize_photo(img, size, bg='#F0F0F0'):
    """把 Tk PhotoImage 最近邻重采样到 size×size（纯 Tk，不依赖 PIL）

    ★ 2026-10-21 为什么要这个：用户给的宝箱图标是 64×64，格子是 48×48。
      Tk 只提供**整数倍** zoom / subsample，64→48 做不出来：
        - 直接塞进去 → Canvas 裁掉四边（金框全没了）
        - subsample(2) → 只剩 32，用户嫌小
      所以自己读像素重做：`get()` 一次拿整图，`put()` 逐行写 48 行
      （48 次 Tcl 调用，6 个图标几十毫秒，可接受）。
      透明像素填 bg（Canvas 底色），视觉上等于透明。
    """
    import tkinter as tk
    w, h = img.width(), img.height()
    if w == size and h == size:
        return img
    out = tk.PhotoImage(width=size, height=size)
    # ⚠ Python 3.12 的 tkinter PhotoImage.get 只接受 (x, y)，不能整块取，
    #   所以按行逐像素读（48×48 = 2304 次调用，实测 6 个图标 < 1 秒，
    #   而且有 _ICON_CACHE，只算一次）。
    for y in range(size):
        sy = min(h - 1, y * h // size)
        cells = []
        for x in range(size):
            sx = min(w - 1, x * w // size)
            try:
                px = img.get(sx, sy)
            except Exception:
                cells.append(bg)
                continue
            if isinstance(px, str):
                cells.append(px if px.startswith('#') else bg)
            elif isinstance(px, (tuple, list)) and len(px) >= 3:
                if len(px) >= 4 and int(px[3]) == 0:
                    cells.append(bg)          # 全透明 → 填底色
                else:
                    cells.append('#%02x%02x%02x'
                                 % (int(px[0]), int(px[1]), int(px[2])))
            else:
                cells.append(bg)
        out.put('{' + ' '.join(cells) + '}', to=(0, y, size, y + 1))
    return out


def box_icon_photo(name, max_side=48):
    """宝箱名字 -> tk.PhotoImage；没有返回 None

    ★ 2026-10-21：图标重采样到正好 max_side×max_side **填满格子**（不裁边、
      也不是缩到 32），数量角标因此正好压在图标右下角内部。
    """
    if not name:
        return None
    key = 'box:%s:%d' % (name, max_side)
    if key in _ICON_CACHE:
        return _ICON_CACHE[key]
    p = _box_icon_map().get(name)
    if not p or not os.path.exists(p):
        _ICON_CACHE[key] = None
        return None
    try:
        import tkinter as tk        # 同 fash9_photo：模块级没有 tk
        img = tk.PhotoImage(file=p)
        if img.width() != max_side or img.height() != max_side:
            img = _tk_resize_photo(img, max_side)
    except Exception as ex:
        print('[!] 宝箱图标加载失败 %s：%s' % (p, ex))
        _ICON_CACHE[key] = None
        return None
    _ICON_CACHE[key] = img           # 必须留引用，否则被 GC 掉变空白
    return img


def box_id_set():
    """读 `刷阵宝箱ID.txt`，返回要显示的物品ID集合

    文件格式（用户 2026-10-21 定稿，Tab 分隔两列）：
        122501<Tab>神风分坛地灵宝箱
        122502<Tab>黑风分坛地灵宝箱

    ★★ 左边那列是 **ItemNameID**，物品ID = ItemNameID - 100000（22501）。
       背包包里下发的是 ItemID，所以这里两个都塞进去，哪个对上都能用。
    ★ 只取每行的第一个数字，避免把名字里的数字（如「神风教教规 3」）误收。
    ★ 每次调用都重读（文件只有几 KB，而 _bag_push 只在背包变化时跑），
      改完文件不用重启程序，重新上线/重读背包就生效。
    """
    ids = set()
    for base in (_APPDIR, getattr(sys, '_MEIPASS', None)):
        if not base:
            continue
        p = os.path.join(base, '刷阵宝箱ID.txt')
        if not os.path.exists(p):
            continue
        try:
            txt = open(p, 'rb').read().decode('utf-8', 'ignore')
        except Exception:
            txt = ''
        for line in txt.splitlines():
            line = line.split('#')[0].strip()
            if not line:
                continue
            first = line.replace('\t', ' ').split()[0].strip()
            if not first.isdigit():
                continue
            v = int(first)
            ids.add(v)
            if v >= 100000:          # ItemNameID -> ItemID
                ids.add(v - 100000)
        break
    return ids


def fash9_photo(name):
    """FASH9_XX -> tk.PhotoImage（48x48 预缩放版），失败返回 None

    ⚠ 2026-10-21 踩坑：`tkinter` 在本文件里是**函数内局部 import** 的，模块级
      没有 `tk` 这个名字。这里如果直接用 tk.PhotoImage，会抛 NameError 被
      except 吞掉 → 静默返回 None → 选择器里 64 个格子全是空白。必须局部导入。
    """
    if not name:
        return None
    if name in _ICON_CACHE:
        return _ICON_CACHE[name]
    import tkinter as tk            # ← 见上面的注释，不能去掉
    d = _fash9_dir()
    if not d:
        return None
    p = os.path.join(d, name + '.png')
    if not os.path.exists(p):
        return None
    try:
        img = tk.PhotoImage(file=p)
    except Exception as ex:
        print('[!] 时装图标加载失败 %s：%s' % (p, ex))
        return None
    _ICON_CACHE[name] = img          # 必须留引用，否则 Tk 会把图回收掉变空白
    return img


def _items_all():
    """整份物品格文件 -> {角色键: {'items': [...]}}"""
    try:
        import json
        with open(_items_path(), encoding='utf-8') as f:
            d = json.load(f)
    except Exception:
        return {}
    if isinstance(d, dict) and isinstance(d.get('roles'), dict):
        out = {}
        for k, v in d['roles'].items():
            if isinstance(v, dict):
                out[str(k)] = v
        return out
    if isinstance(d, dict) and 'items' in d:          # 旧/简陋格式兜底
        return {SLOT_DEFAULT_KEY: d}
    return {}


def load_items(key=None):
    """读回某角色的 6 个指定物品 ID；没有就全 0

    key=None 时退回 "__default__"，和技能格的处理保持一致（新录入的角色
    先继承默认那一套，免得升级后又要重新配）。
    """
    k = str(key) if key else SLOT_DEFAULT_KEY
    all_it = _items_all()
    d = all_it.get(k)
    if d is None and SLOT_DEFAULT_KEY in all_it:
        d = all_it.get(SLOT_DEFAULT_KEY)
    d = d or {}
    try:
        a = [int(x or 0) for x in (d.get('items') or [])][:N_ITEM_SLOT]
    except Exception:
        a = []
    while len(a) < N_ITEM_SLOT:
        a.append(0)
    return a


def save_items(ids, key=None):
    """只覆盖该角色那一份，别的角色原样保留"""
    try:
        import json
        k = str(key) if key else SLOT_DEFAULT_KEY
        all_it = _items_all()
        all_it[k] = {'items': [int(x or 0) for x in ids][:N_ITEM_SLOT]}
        tmp = _items_path() + '.tmp'
        with open(tmp, 'w', encoding='utf-8') as f:
            json.dump({'version': 2, 'roles': all_it}, f,
                      ensure_ascii=False, indent=1)
        os.replace(tmp, _items_path())
    except Exception:
        pass


# ================================================================ 角色档案（录入）
#   用户 2026-10-21 要求：左侧登录/选角保留，最后一步从「进入游戏」改成「录入」；
#   录入的结果进中间的角色列表，之后在列表里选中角色 → 右侧点「上线」。
#   档案里存的是「重新登录并进这个角色」所需的最小信息：
#     acct/pwd + 大区名 + 分区名 + 大世界线路名 + 角色名
#   大区/分区/线路都存**名字**：服务端每次下发的 id / ip 可能变，名字最稳。
def _arch_path():
    return os.path.join(_APPDIR, '角色档案.json')


def arch_key(acct, zone, name):
    """档案唯一键：账号 + 分区 + 角色名（同名不同区/不同账号互不覆盖）"""
    return '%s|%s|%s' % ((acct or '').strip(), (zone or '').strip(),
                         (name or '').strip())


def load_arch():
    """-> list[dict]，坏文件当空表，不崩"""
    try:
        import json
        with open(_arch_path(), encoding='utf-8') as f:
            d = json.load(f)
        rows = d.get('roles') if isinstance(d, dict) else d
        out = []
        for r in (rows or []):
            if isinstance(r, dict) and r.get('name'):
                out.append(r)
        return out
    except Exception:
        return []


def save_arch(rows):
    try:
        import json
        tmp = _arch_path() + '.tmp'
        with open(tmp, 'w', encoding='utf-8') as f:
            json.dump({'version': 1, 'roles': rows}, f,
                      ensure_ascii=False, indent=1)
        os.replace(tmp, _arch_path())
    except Exception:
        pass


# ★ 用户要求（2026-10-20）：**图标占满整个格子、下面不显示汉字名字**。
#   格子 52×50，图标直接铺满 52×50（不再是 46×46 的小方块），边框画进像素里。
#   原始图 64×64 是 RGBA（带透明通道），缩放必须自己算，见 _icon_fit。


def _icon_dirs():
    """技能图标的查找目录，按优先级排：
       1) 程序同级/技能图标     —— 自己丢进去的新图标放这里，优先级最高
       2) exe 内部/技能图标     —— 打包时带进去的那批（sys._MEIPASS）
    """
    ds = [os.path.join(_APPDIR, '技能图标')]
    mp = getattr(sys, '_MEIPASS', None)
    if mp:
        p = os.path.join(mp, '技能图标')
        if p not in ds:
            ds.append(p)
    return ds


def _icon_path(sid):
    """技能图标文件，找不到返回 None

    ★★ 两种命名都认（2026-10-20 用户给了 16 张按**技能名**命名的图标）：
        技能图标/<技能ID>.png    —— 精确到某一级（同名技能不同等级可以各放一张）
        技能图标/<技能名>.png    —— 同一技能的所有等级共用一张
      先找 ID，找不到再退回名字 —— 这样以后抓到分级图标，只要丢进目录就自动生效，
      不用改代码，也不用把 7000 多个 ID 各存一份。
    """
    cands = ['%d' % int(sid)]
    try:
        _nm = (((skill_cfg(sid) or {}).get('name')) or '').strip()
        if _nm:
            cands.append(_nm)
    except Exception:
        pass
    for d in _icon_dirs():
        for base in cands:
            for ext in ('.png', '.gif'):
                p = os.path.join(d, base + ext)
                if os.path.exists(p):
                    return p
    return None


def _icon_fit(img, tw, th=None, gray=False):
    """把图标缩到 tw×th（th 省略就正方形），**保住透明通道**

    Tk 自带的 zoom / subsample 只能整倍缩放：64→52 根本凑不出来，
    硬凑成 64→48 也要先抽成 16×16 再放大 3 倍，细节全丢。所以自己做
    **盒式平均**：每个输出像素 = 源图对应小方块里「不透明」像素的均值。

    ★★ 透明像素绝不能参与平均 —— 图标四角是透明的，混进去就是一圈灰黑糊边；
       整块全透明的地方要显式 transparency_set，否则会变成黑块。
    ★ gray=True 直接在采样时算亮度，省一次整图重扫（冷却置灰用）。
    """
    th = tw if th is None else th
    try:
        w, h = img.width(), img.height()
        if (w, h) == (tw, th) and not gray:
            return img
        rows, masks = [], []
        for y in range(h):
            row, msk = [], []
            for x in range(w):
                row.append(img.get(x, y))
                msk.append(not img.transparency_get(x, y))
            rows.append(row)
            masks.append(msk)
        out = img.__class__(width=tw, height=th)
        for oy in range(th):
            y0 = oy * h // th
            y1 = max(y0 + 1, (oy + 1) * h // th)
            for ox in range(tw):
                x0 = ox * w // tw
                x1 = max(x0 + 1, (ox + 1) * w // tw)
                r = g = b = n = 0
                for yy in range(y0, y1):
                    mrow, crow = masks[yy], rows[yy]
                    for xx in range(x0, x1):
                        if not mrow[xx]:
                            continue
                        c = crow[xx]
                        r += c[0]
                        g += c[1]
                        b += c[2]
                        n += 1
                if not n:
                    out.transparency_set(ox, oy, True)
                    continue
                r //= n
                g //= n
                b //= n
                if gray:
                    v = (r * 299 + g * 587 + b * 114) // 1000
                    r = g = b = v
                out.put('#%02x%02x%02x' % (r, g, b), (ox, oy))
        return out
    except Exception:
        # 老 Tk 没有 transparency_get → 退回整倍缩放，最多糊一点
        try:
            w0, h0 = img.width(), img.height()
            fw = Fraction(tw, w0).limit_denominator(16)
            fh = Fraction(th, h0).limit_denominator(16)
            if fw.denominator > 1 or fh.denominator > 1:
                img = img.subsample(max(1, fw.denominator),
                                    max(1, fh.denominator))
            if fw.numerator > 1 or fh.numerator > 1:
                img = img.zoom(max(1, fw.numerator), max(1, fh.numerator))
        except Exception:
            pass
        return img


def gray_photo(img):
    """PhotoImage 黑白化（没有 PIL，逐像素算亮度）—— 冷却中的图标用

    ★ 透明像素原样留透明：读出来是 (0,0,0)，直接算亮度会把图标四角涂成黑块。
    """
    try:
        g = img.__class__(width=img.width(), height=img.height())
        for y in range(img.height()):
            for x in range(img.width()):
                if img.transparency_get(x, y):
                    g.transparency_set(x, y, True)
                    continue
                c = img.get(x, y)
                v = (c[0] * 299 + c[1] * 587 + c[2] * 114) // 1000
                g.put('#%02x%02x%02x' % (v, v, v), (x, y))
        return g
    except Exception:
        return img


# ================================================================ 技能格边框
# ★★ 选中边框的配色取自 技能图标/选中边框源.png（用户给的 64×64 绿框素材）。
#    源图边框只有 4px 厚，直接缩到 52×50 会糊成一团灰绿，所以按逐像素剖面
#    归纳出的色阶在目标尺寸上**重画**：外 1px 近黑描边 → 深翡翠 → 翡翠 →
#    亮绿高光 → 内侧收边。小尺寸下反而比整图缩放更清晰。
#    深度 p = 从外边界往里的像素距离（0 = 最外沿），按 p 在色阶间线性插值。
# ★ 2026-10-21 加粗（用户两度要求：先说细、再点名要 4px）：
#   3.6px → 4px，并且**最外沿压一道近黑深绿描边**、主体拉到 #00FF6B 满饱和，
#   在浅色面板上一眼就能看出哪几格在连招里。
#   剖面（p = 从外边界往里的像素距离）：
#     0.0px 近黑深绿 → 0.5px 翠绿 → 1.3px 亮绿高光 → 2.5px 主色 → 3.3px 收深 → 4.0px 内沿
_RING_SEL = ((0.00, (0x07, 0x33, 0x22)),
             (0.50, (0x00, 0xB8, 0x60)),
             (1.30, (0x00, 0xFF, 0x6B)),
             (2.50, (0x00, 0xE2, 0x6C)),
             (3.30, (0x09, 0x86, 0x42)),
             (4.00, (0x04, 0x33, 0x1F)))
_RING_OFF = ((0.00, (0x7C, 0x8A, 0x87)),
             (0.60, (0xAD, 0xB8, 0xB5)),
             (1.40, (0xD8, 0xDE, 0xDC)))
RING_T_SEL = 4.0                     # ★ 选中边框厚度（px）—— 用户点名要 4px
RING_T_OFF = 1.8                     # 未选中只留一道细浅灰线
_RING_CACHE = {}


def _lerp_rgb(stops, p):
    """按深度 p 在色阶里取色"""
    prev_p, prev_c = stops[0]
    for lim, c in stops[1:]:
        if p <= lim:
            k = 0.0 if lim <= prev_p else (p - prev_p) / (lim - prev_p)
            return tuple(int(prev_c[i] + (c[i] - prev_c[i]) * k) for i in range(3))
        prev_p, prev_c = lim, c
    return stops[-1][1]


def _ring_pixels(w, h, sel, radius=5.0):
    """预计算圆角边框：返回 [(x, y, (r,g,b), 覆盖度)]，覆盖度 0~1 用于抗锯齿

    用圆角矩形的**距离场**判断像素在不在边框带里：d 落在 [0, 厚度] 就是边框，
    d 越大越靠里。每个像素取 3×3 采样点算覆盖率 —— 圆角处不这么做就是锯齿。

    ★ 只扫靠近四条边的像素（离最近边 > 厚度+1.5 的整片中间直接跳过），
      52×50 只算 ~800 个点，结果按 (尺寸, 是否选中) 缓存，全程只算一次。
    """
    key = (w, h, bool(sel), radius)
    if key in _RING_CACHE:
        return _RING_CACHE[key]
    sel = bool(sel)
    stops = _RING_SEL if sel else _RING_OFF
    t = RING_T_SEL if sel else RING_T_OFF
    cx, cy = w / 2.0, h / 2.0
    hx, hy = w / 2.0 - radius, h / 2.0 - radius

    def df(x, y):
        """返回像素中心到**图像外边界**的深度：0 = 最外沿，越大越靠里

        ★ 2026-10-21 修：以前这里把矩形半宽写成 hx = w/2 - radius 之后
          又没做 min(max(q,0)) 的内侧修正，导致 d=0 的等值线落到了离边
          4~5px 的地方 —— 4px 的边框最后只画出 1 个像素（用户说「太细」
          其实一直是这个 bug，调厚度参数根本没用）。
          标准圆角矩形 SDF 取负号才是「往里的深度」。
        """
        qx = abs(x + 0.5 - cx) - hx
        qy = abs(y + 0.5 - cy) - hy
        ax, ay = (qx if qx > 0 else 0.0), (qy if qy > 0 else 0.0)
        sd = (ax * ax + ay * ay) ** 0.5 + min(max(qx, qy), 0.0) - radius
        return -sd

    out = []
    for y in range(h):
        for x in range(w):
            if min(x, y, w - 1 - x, h - 1 - y) > t + 1.5:
                continue                 # 中间大片区域，扫都不扫
            n = 0
            acc = 0.0
            for sy in (0.17, 0.5, 0.83):
                for sx in (0.17, 0.5, 0.83):
                    d = df(x + sx, y + sy)
                    if 0.0 <= d <= t:
                        n += 1
                        acc += d
            if n:
                out.append((x, y, _lerp_rgb(stops, acc / n), n / 9.0))
    _RING_CACHE[key] = out
    return out


def _cell_photo(icon, w, h, sel, fill='#FFFFFF'):
    """合成一整格：图标铺满 + 边框，返回不透明 PhotoImage

    ★ 为什么不在界面上套两个控件：Tk 的 Label **不跟下面的控件做 alpha 合成**，
      透明处露的是它自己的底色。所以边框直接画进像素里，一次 put 画完；
      选中/未选中只是换一张图，图标位置不会跳。
    """
    import tkinter as tk
    if icon is not None:
        rows = []
        for y in range(h):
            row = []
            for x in range(w):
                if icon.transparency_get(x, y):
                    row.append(fill)
                else:
                    c = icon.get(x, y)
                    row.append('#%02x%02x%02x' % (c[0], c[1], c[2]))
            rows.append(row)
    else:
        rows = [[fill] * w for _ in range(h)]
    for x, y, c, cov in _ring_pixels(w, h, sel):
        if cov >= 0.999:
            rows[y][x] = '#%02x%02x%02x' % c
        else:
            b = rows[y][x]
            rows[y][x] = '#%02x%02x%02x' % tuple(
                int(int(b[1 + 2 * i:3 + 2 * i], 16) * (1.0 - cov) + c[i] * cov)
                for i in range(3))
    img = tk.PhotoImage(width=w, height=h)
    img.put('{' + '} {'.join(' '.join(r) for r in rows) + '}')
    return img


def _app_dir():
    """程序的数据目录（配置 json / 日志 / 图标都在这下面）

    ★ 2026-10-21：为安卓（Kivy 版）加了一条 —— 安卓上程序在 APK 私有目录里，
      `__file__` 那个路径**不可写**，配置文件必须落到 App 给的 user_data_dir。
      所以先看环境变量 JG_APPDIR；PC 上没设这个变量，行为和以前完全一样。
    """
    _env = (os.environ.get('JG_APPDIR') or '').strip()
    if _env:
        try:
            os.makedirs(_env, exist_ok=True)
            return _env
        except Exception:
            pass
    return os.path.dirname(os.path.abspath(
        sys.executable if getattr(sys, 'frozen', False) else __file__))


_APPDIR = _app_dir()
LOGPATH = os.path.join(_APPDIR, '极光助手_log.txt')
try:
    _LOGF = open(LOGPATH, 'w', encoding='utf-8')
except Exception:
    _LOGF = None

# ---- 0x111 登录包模板（576 字节 = 4B头 + 568B载荷 + 4B尾；取自 p1_template.txt，已内嵌）----
# ★★★ 这个字节串必须严格 576 字节，少一个字节都会让整包错位 → 服务端返回 result=0 ★★★
LOGIN_TPL_HEX = (
    '7104110101000000676b36323335313300000000000000000000000000000000000000000000000000000000000000000000'
    '00000000000000000000000000000000000000000000002d4ff634364188e9d7cd67d0de1d141ae2a9bd2885e2ab8e62e139'
    'a45b990302fed7de85f45cfe70fe9066701e44ef95d92da5ecab2a03fa84180a95e132c45e07000000000000000000000000'
    '0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000'
    '0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000'
    '0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000'
    '0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000'
    '0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000'
    '0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000'
    '0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000'
    '0000000000000000000000000000000000000000630000008e030000ecd1c74243303a42463a42453a39333a34363a324500'
    '1a0090ac742218ee1a00ffffffff01010000000000000000c96c'
)
assert len(bytes.fromhex(LOGIN_TPL_HEX)) == 576, '登录模板必须 576 字节'


# ================================================================ 协议层
def s16(v):
    v &= 0xFFFFFFFF
    return v - 0x100000000 if v >= 0x8000 else v


def jg_cksum(data):
    """种子 0x5AA5 的 RFC1071 变体（移植自客户端 FUN_00ae7dc0）"""
    c = 0x5AA5
    n = len(data); i = 0
    while n > 1:
        c += data[i] | (data[i + 1] << 8); i += 2; n -= 2
    if n:
        c += data[i]
    i2 = (c >> 16) + (c & 0xFFFF)
    return (~(((i2 >> 16) & 0xFFFF) + s16(i2))) & 0xFFFF


def wframe(cmd, payload=b''):
    """统一封包（flag=1，带 4 字节尾 [u16 0][u16 校验和]）"""
    hdr = (cmd << 16) | ((len(payload) & 0x7FFF) << 1) | 1
    return struct.pack('<I', hdr) + bytes(payload) + b'\x00\x00' + \
        jg_cksum(payload).to_bytes(2, 'little')


def parse_frames(buf, with_tail=True):
    out, i = [], 0
    while i + 4 <= len(buf):
        u = struct.unpack('<I', buf[i:i + 4])[0]
        cmd, ln, fl = u >> 16, (u >> 1) & 0x7FFF, u & 1
        tot = 4 + ln + (4 if (fl and with_tail) else 0)
        if i + tot > len(buf):
            break
        out.append((cmd, fl, bytes(buf[i + 4:i + 4 + ln])))
        i += tot
    return out, i


def gbk(b):
    return b.split(b'\x00')[0].decode('gbk', 'ignore')


def _rl(b, i):
    n = b[i]; i += 1
    if n & 0x80:
        k = n & 0x7F
        n = int.from_bytes(b[i:i + k], 'big'); i += k
    return n, i


def der_pub(b):
    i = 1
    ln, i = _rl(b, i)
    e = i + ln
    v = []
    while i < e:
        i += 1
        l, i = _rl(b, i)
        v.append(int.from_bytes(b[i:i + l], 'big')); i += l
    return v[0], v[1]


def pkcs1_v15(n, e, m):
    k = (n.bit_length() + 7) // 8
    while True:
        ps = os.urandom(k - len(m) - 3)
        if b'\x00' not in ps:
            break
    return pow(int.from_bytes(b'\x00\x02' + ps + b'\x00' + m, 'big'), e, n).to_bytes(k, 'big')


def roles_from_205(pl):
    """解析 0x205 角色列表：[0x10]=数量，[0x11:]=角色名(GBK)，[0x02:0x06]=角色号，[0x27:]=26 位数字 ID"""
    out = []
    if len(pl) < 0x30:
        return out
    cnt = pl[0x10]
    cid = int.from_bytes(pl[2:6], 'little')
    nm = gbk(pl[0x11:])
    did = pl[0x27:0x41].split(b'\x00')[0].decode('ascii', 'ignore')
    if nm:
        out.append({'name': nm, 'cid': cid, 'id': did})
    # 多角色兜底：扫所有 26 位数字串，取其前面紧邻的 GBK 名
    if cnt > 1:
        i = 0
        while i < len(pl) - 26:
            seg = pl[i:i + 26]
            if all(0x30 <= ch <= 0x39 for ch in seg):
                j = i - 1
                while j > 0 and pl[j] == 0:
                    j -= 1
                st = j
                while st > 0 and pl[st - 1] >= 0x20 and pl[st - 1] != 0:
                    st -= 1
                nm2 = gbk(pl[st:i])
                if nm2 and all(x['id'] != seg.decode() for x in out):
                    out.append({'name': nm2, 'cid': 0, 'id': seg.decode()})
                i += 26
            else:
                i += 1
    return out


def worldlines_from_213(pl):
    """解析 0x213 大世界线路表"""
    out = []
    key = '大世界线路'.encode('gbk')
    k = 0
    while True:
        i = pl.find(key, k)
        if i < 0:
            break
        k = i + 1
        nm = gbk(pl[i:])
        v1 = int.from_bytes(pl[i + 0x10:i + 0x14], 'little')
        v2 = int.from_bytes(pl[i + 0x14:i + 0x18], 'little')
        ip = pl[i + 0x18:].split(b'\x00')[0].decode('ascii', 'ignore')
        out.append({'name': nm, 'ip': ip, 'v1': v1, 'v2': v2})
    return out


# ================================================================ 客户端
class Client(threading.Thread):
    """后台线程：所有网络操作都在这里做，事件用队列推给界面"""

    def __init__(self, ev):
        super().__init__(daemon=True)
        self.ev = ev
        self.tag = ''                   # 日志前缀（角色名），多开用
        # ★ 2026-10-21 排障：记录最近收到的帧（命令号 + 载荷长度）。
        #   服务端「握手后只回两帧就把连接 RST」的时候，靠它看清到底回了什么。
        self.last_cmds = []
        self.cmds = queue.Queue()
        self.running = True
        self.rhythm = True
        self.abort = False              # 界面点「停止/下线」时打断阻塞流程

        self.ls = None                  # 登录服 socket
        self.w = None                   # World socket
        self.buf = bytearray()
        self.off = 0
        self.token = None
        # ★★★ 2026-10-21 重大发现：这个 4 字节魔数**不是固定值**！
        #   登录服在 0x113 应答的 @4..7 会给**每个账号**一个自己的值：
        #     gk623513 → f3 f3 0d 04
        #     gk656929 → f7 f3 0d 04
        #   后面连 World（0x207）和所有 World 侧请求（0x201/0x202/0x205/0x401）
        #   都必须用**服务端给的这个值**。以前写死 f3f30d04，只有恰好拿到 f3 的
        #   账号能进，其它账号 World 握手直接 0x20C flag=1 被拒 ——
        #   这就是"只有 gk623513 能读到角色、别的账号一个都读不到"的真正原因。
        #   （也解释了 v3.3 为什么"按抓包"改成 f6：那个号当时拿到的就是 f6。）
        self.magic = b'\xf3\xf3\x0d\x04'   # do_login 成功后会被 0x113 @4..7 覆盖
        self.last_113 = b''             # 诊断用：上次登录成功的 0x113 原始载荷
        self._host, self._port = LOGIN_HOST_DEF, LOGIN_PORT_DEF
        self._acct = self._pwd = ''
        self.areas = []                 # 大区（0x121）
        self.lines = []                 # 分区（0x117）
        self.roles = []
        self._roles_seen = set()
        self.roles_last_t = 0.0
        self.wlines = []
        self.cur_line = None            # 当前 World 对应的分区
        self.pick_role = None
        self.pick_wline = None
        self.picked_cid = None          # 已经在 World 上选好的角色号
        self._char_idx = None           # 0x20f 里带的角色序号
        self._t_world_closed = 0.0      # 上次断开 World 的时刻（用于重连前留间隔）

        self.state = 'idle'
        self.err = ''
        self.in_world = False
        self.t_inworld = 0.0
        self.hb_count = 0
        self.nrecv = 0
        self.nframes = 0
        self.last_hb = 0.0
        self.hb = 0
        self.hb_t = 0.0
        # ★ 2026-10-17 新增：服务端权威时钟（0x71d 每 ~12.9 秒广播一次）
        #   0x798 只是回显我们发出的值，不能当基准；真正的基准是 0x71d
        self.srv_hb = 0
        self.srv_hb_t = 0.0
        self.hb_ack_t = 0.0            # 上次收到 0x798 应答的时刻（3 秒无应答则重发）
        self.sent201 = False
        self.sent202 = False
        self.sent401 = False
        self.sent4b0 = False
        self.map_id = None
        self.map_name = ''
        self.pos = None
        self.pos_set_t = 0.0            # 最近一次 0x407 设位时间
        self._pos_unconfirmed = 0.0     # 已发 0x407 但还没收到服务端 0x62b 回执
        self.online_role = None         # 当前在线角色 dict

        # ---- 进入场景序列（收到 0x603 立刻开跑）----
        self.scene = {'seq': None, 'i': 0, 'done': False, 't0': 0.0}
        self.aoi_hs = False             # 0x47e 握手首查是否已发
        self.wtime = 0                  # 0x41d 用的世界时间

        # ---- 实体台账：0x647 给名字+初始坐标，0x62B 给实时坐标，0x623 给血量 ----
        self.ent = {}                   # eid -> {x,y,z,name,hp,hpmax,t}
        self.ent_seen = set()           # 0x647 出现过的实体 ID（去重）
        self.ent_pend = []              # 待用 0x47e 查详情
        self.ent_queried = set()
        self._t_query = 0.0
        self.rp_npc = set()             # 已申报 0x46E
        self.rp_tc = set()              # 已申报 0x474
        self.rp_stat = set()            # 已申报 0x46D/0x46F/0x471/0x473
        self.rp_pl = set()              # 已订阅 0x46C（附近玩家）
        self.rp_req = set()             # 已主动要过身份的实体（0x46E Req）

        # ---- 服务端自带自动战斗（0x4C7）----
        self.bot_on = False
        self.bot_last = 0.0
        self.bot_stat_t = 0.0
        self.bot_kills = 0

        # ---- 自己打怪（0x408）----
        self.last_atk_t = 0.0
        self.atk_sent = 0
        self.atk_ack = 0                # 服务端 0x648 受理次数
        self.atk_hit = 0                # 我方 0x610 命中广播次数
        self.skill_cd = {}              # 技能ID -> 冷却到期的 time.time()
        self.skill_seen = {}            # 0x648 收录到的 技能ID -> 冷却ms
        self.grp_cd = 0.0               # 整组公共CD到期时刻（0x648 key=0 那 1500ms）
        # ⚠ 通用技能格 2026-10-20 起改纯手动（点一下放一次），
        #   buff_skills / buff_last / _buff_step 已全部移除，别再加回来。
        self.my_cls = 0                 # 从服务端受理过的技能反推出来的职业（ClassReq）
        self.probe = None               # 技能探测状态机（None = 没在探测）
        self.sweep = None               # 「试一遍」状态机（全部已学技能挨个试）
        self.skill_ack_ids = set()      # 收到过 0x648 / 0x60A 的技能ID
        self.learned = set()            # 0x625 下发的「已学会技能」ID
        self._learned_sig = None        # 上次打日志用的指纹，防重复刷屏
        self._grp_cd_log = 0            # 「整组CD初始化」日志只打前几条
        self.use_sent = 0               # 「使用」按钮成功发出的次数
        self.use_ack = 0                # 其中被服务端 0x60A 确认「真放了」的次数
        self._use_t = 0.0               # 最近一次「使用」的时间
        self._use_skill = 0             # 最近一次「使用」的技能ID
        self._last_ack_t = 0.0          # 最近一次「施法成功」时间（0x648 或 0x60A）
        self._ack_skill = 0             # 最近受理的技能ID
        self._cast_log = 0              # 施法成功日志只打前几条
        self._noack_n = 0               # 连续没回应的次数（用于诊断提示）
        # ---- 技能组合（连招）：按顺序循环放 ----
        self.combo = []                 # [(技能ID, 组, step), ...]
        self.combo_i = 0                # 当前轮到第几招
        self.combo_t = 0.0              # 下一招最早可以发的时间
        self.atk_target = 0
        # ---- 自身状态（0x623 / 0x646）----
        self.hp = None                  # 当前血量（0x623 attr 3001）
        self.hp_max = None              # 血量上限（0x623 attr 2008）
        # ★ 2026-10-21 新增：等级 / 经验（用户要求「角色信息里读出等级和经验」）
        #   0x60F PlayerExpUpdate 结构（录制实证，30 字节）：
        #     [0:4]  cid
        #     [4]    等级          ← 与 0x623 attr 5001 逐一对应，已验证
        #     [5:8]  固定前缀 0x2f65（沿用不动）
        #     [8:16] 0
        #     [16:20] 当前等级内的经验
        #     [20:24] 升到下一级所需经验
        #     [24:30] 0
        #   另外 0x623 也会带 attr 5001（等级）/ 3009（经验），两条路都收。
        self.level = None
        self.exp = None
        self.exp_need = None
        self.mp = None                  # 当前法力（attr 3002）
        self.mp_max = None              # 法力上限（attr 2009）
        self.dead = False               # 是否已死亡
        self.hp_t = 0.0
        self.relive_try = 0             # 复活尝试序号（0/1/2 对应 type 序列）
        self.relive_last = 0.0
        self._relive_pending = False
        self.auto_atk = False
        self.auto_atk_skill = None      # (skill, group, step)
        # ★ 2026-10-21 新增：自动同意组队（收到 0x684/0x685/0x686 确认请求就回 Ret）
        self.auto_team = False
        self.team_mates = []            # 队伍成员 cid 列表（0x68E 累加，0x68F/0x69A 清空）
        self._team_auto_n = 0           # 本次上线已自动同意次数（日志统计用）
        # ★ 2026-10-21 新增：血/蓝低于阈值时自动放凝神术（用户要求）
        #   阈值是百分比（1~99），血**或**蓝任一项低于就放，由玩家在界面上选。
        #   凝神术 = 自我施法（SELFCAST 里的 1005，真包实测 组391/step5/目标自己）。
        #   ⚠ 用户口报的 ID 是 10005，客户端 Skillstudy 表里其实叫 1005，
        #     两个都认（heal_skill_id() 先看本角色学到了哪个）。
        self.auto_heal = False
        self.auto_heal_pct = 30
        self._heal_t = 0.0              # 上次自动施法时间（节流，别一掉血就连发）
        self._heal_tick_t = 0.0         # 上次周期检查时间（见 _heal_tick）
        self._heal_hp0 = None           # 上次施法时的血/蓝（判断「放了到底有没有回」）
        self._heal_mp0 = None
        self._heal_n = 0                # 本次上线自动放了几次（日志统计）
        self._heal_sid = 0              # 实际用的技能 ID（第一次定下来就缓存）
        # ★ 2026-10-21 新增：背包（0x613 PlayerItemOperation）
        #   112 字节一条，录制实证结构：
        #     [0]     操作类型（3 = 槽位数据）
        #     [1]     容器：1=主背包  2=装备栏  5=?
        #     [2:4]   槽位索引（u16）
        #     [8:10]  物品 ID（u16）
        #     [10:12] 数量（u16）
        #   42 条实测里 容器1 占 31 条（槽位 0-31），就是主背包。
        self.bag = {}                   # {(container, slot): {'iid': int, 'n': int}}
        self._use_loop = None           # 「用完为止」的循环状态（_tick 驱动）
        self._bag_t = 0.0               # 上次把「箱子清单」推给界面的时刻（节流）
        self._bag_ask_t = 0.0           # 进世界后补要背包的时间点（0=不需要）
        self._bag_seen = 0              # 已收到的 0x613 槽位帧数（诊断用）
        self._bag_dump = 0              # 已 dump 过原始 hex 的帧数（最多 8）
        self._bag_dirty = False         # 有新槽位数据、还没推给界面
        self._bag_warn_t = 0.0          # 进世界后「背包一直空」的告警时间点
        self._npcs_t = 0.0
        self.radius = RADIUS            # 检测半径（米），界面可改
        self._diag = {}                 # 上次 _npc_list 的过滤统计，用于解释"为什么没怪"
        self._6b9_log = 0               # 0x6B9 身份包只打前几条日志
        self._unk_mnid = 0              # MNID 查不到表时只提示前几条
        self._need_aoi = 0.0            # 传送后要重新拉一次场景实体
        self._aoi_t = 0.0               # ★ 上次「轻刷新」视野的时刻（实时刷新用）
        self._nofind_t = 0.0            # ★ 开着自动打却一直找不到目标的起始时刻
        self._aoi_n = 0                 # 轻刷新次数（日志节流用）
        self.bl = load_blacklist()      # ★ 怪物排除名单（按名字），刷新出来也不打
        self.n6b9 = 0                   # ★ 收到的 141 字节身份包数（诊断用）
        self.n6b9o = 0                  # ★ 0x6B9 的其它长度变体数
        self._ident_try = {}            # ★ 实体ID -> 补查身份次数（没名字的补查）
        self._ident_last = {}           # ★ 实体ID -> 上次补查时刻
        self._ident_t = 0.0             # ★ 上次补查整轮的时刻
        self._tgt_fail = {}             # 实体ID -> 连续「服务端没反应」次数
        self._skip_t = {}               # 实体ID -> 解禁时刻（打不动的怪先跳过）
        self.show_npc = False           # 列表里是否也显示 NPC（排障用）
        self.dump_rx = False            # 是否把收到的包全记到文件（排障用）
        self._rxfile = None
        self._hint_t = 0.0              # 上一次「打不了」类提示的时间（节流用）
        self._mp_hint_t = 0.0           # 上一次「没蓝了」提示的时间
        self._skill_mp_cost = {}        # 技能 → 实测耗蓝（从 0x623 下降量自学）
        self._skill_hp_cost = {}        # 技能 → 实测耗血（血祭这类烧血的）
        self._mp_seen_max = 0           # 见过的最高蓝量（2009 不下发时兜底）
        self._attr_seen = {}            # 诊断：attr ID -> 首次值（每上线一次清空）
        self.summon_t = {}              # 前置技能 -> 最近一次放成功的时刻
        self._noack_sk = {}             # 技能 -> 连续无回应力（诊断用）
        self._ack_watch = False         # 发出去一招，正在等服务端理
        self._lowmp_t = 0.0             # 上次「蓝量低」提醒时刻
        self._last_cast_sk = 0          # 最近一次发出的技能ID
        self._last_cast_t = 0.0         # 最近一次发技能的时间

    # ---------------- 基础工具
    def log(self, s):
        # ★ 2026-10-21 多开：多个角色同时在线时日志混在一个文件里，
        #   加个角色名前缀才分得清是谁在说话（tag 由界面在创建会话时设置）
        _tag = getattr(self, 'tag', '')
        line = '[%s]%s %s' % (time.strftime('%H:%M:%S'),
                              ('[%s]' % _tag) if _tag else '', s)
        # ★ 2026-10-21 多线程录入：界面上也会有**多条录入连接**同时说话，
        #   所以事件里带上 tag，不然"登录账号A"和"登录账号B"的日志会分不清。
        self.ev.put(('log', ('[%s] %s' % (_tag, s)) if _tag else s))
        if _LOGF is not None:
            try:
                _LOGF.write(line + '\n')
                _LOGF.flush()
            except Exception:
                pass

    def st(self, **kw):
        self.ev.put(('state', kw))

    def st_tick(self, **kw):
        """周期状态：限流到 ~4 次/秒，避免刷爆界面事件队列"""
        now = time.time()
        if now - getattr(self, '_st_t', 0.0) < 0.25:
            return
        self._st_t = now
        self.ev.put(('state', kw))

    def post(self, cmd, **kw):
        if cmd in ('logout', 'stop'):
            self.abort = True
        self.cmds.put((cmd, kw))

    def hb_now(self):
        """世界时钟（毫秒）。★ 2026-10-17 抓包校正 —— 原实现基准取错，是 180 秒掉线的根因。

        真客户端实测（220 秒抓包）：
          心跳 0x50f 的值 = (GetTickCount - 本地基准) + 服务端基准时钟，
          且必须与服务端时钟对齐（偏差仅 ±50ms）。
        基准来源优先级：
          1) 0x71d 服务端时钟广播（每 12.9 秒一次，权威）   ← 新增
          2) 0x798 心跳应答（只是回显我们发出的值，退而求其次）
          3) HB_BASE 兜底
        用错基准会造成约 15.8 小时偏差 → 服务端判定客户端异常 → 约 180 秒被踢。
        """
        if self.srv_hb:
            return (self.srv_hb + int((time.time() - self.srv_hb_t) * 1000)) & 0xFFFFFFFF
        if self.hb:
            return (self.hb + int((time.time() - self.hb_t) * 1000)) & 0xFFFFFFFF
        return (HB_BASE + int((time.time() - self.t_inworld) * 1000)) & 0xFFFFFFFF

    def _pace(self, sec, jitter=0.18):
        """带抖动的等待（等待期间照常收包）"""
        if not self.rhythm:
            return
        self.pump(sec * (1.0 + random.uniform(-jitter, jitter)))

    def _micro(self, lo=0.10, hi=0.30):
        if not self.rhythm:
            return
        self.pump(random.uniform(lo, hi))

    # ---------------- 收发泵
    def _parse_buf(self):
        while self.off + 4 <= len(self.buf):
            u = struct.unpack('<I', self.buf[self.off:self.off + 4])[0]
            cmd, ln, fl = u >> 16, (u >> 1) & 0x7FFF, u & 1
            if self.off + 4 + ln > len(self.buf):
                break
            pl = bytes(self.buf[self.off + 4:self.off + 4 + ln])
            self.off += 4 + ln
            try:
                self.handle_frame(cmd, pl)
            except Exception as ex:
                self.log('[!] 处理 0x%03x 出错：%s' % (cmd, ex))
        if self.off > 65536:
            del self.buf[:self.off]
            self.off = 0

    def _tick(self):
        # 角色列表：最后一帧 0x205 之后安静 1 秒 → 判定收全
        if (self.roles_last_t and self.state != 'roles' and not self.in_world
                and time.time() - self.roles_last_t > 1.0):
            self.state = 'roles'
            self.roles_last_t = 0.0
            self.log('   ★ 角色列表读取完成：共 %d 个' % len(self.roles))
            self.st(step='⑤ 角色已就绪', nroles=len(self.roles))
        # ★ 施法回响看守：发出去 1.5 秒服务端还没理 → 打一条诊断，
        #   把「没蓝/没血/冷却/前置不满足/没学」连现状数字一起列出来。
        #   （服务端对放不出来的技能是静默丢弃，不查这个用户根本看不出原因）
        if self._ack_watch and time.time() - self._last_cast_t > 1.5:
            self._ack_watch = False
            if self._last_ack_t < self._last_cast_t:
                self._cast_note_fail(self._last_cast_sk)
        # ★ 进入场景序列：收到 0x603 后必须跑完，否则服务端不收世界交互包
        if self.in_world and not self.scene['done']:
            self._scene_step()
        # ★ 传送之后重新拉一次周围实体（等服务端把 0x407 落库）
        if self.in_world and self._need_aoi and time.time() - self._need_aoi >= 0.8:
            self._need_aoi = 0.0
            self._resync_scene(clear=True)
        # ★★ 怪物实时刷新（2026-10-20 用户要求）：
        #   站桩不动时服务端不会主动把「新刷出来的怪」推过来，
        #   所以每隔 AOI_REFRESH_SEC 重发一次视野 + AOI 握手，让它重新下发清单。
        #   这是**轻刷新**：只重发请求，不清台账（清了会把血量/身份都丢了）。
        if self.in_world and self.scene['done'] and AOI_REFRESH_SEC > 0:
            if not self._aoi_t:
                self._aoi_t = time.time()
            elif time.time() - self._aoi_t >= AOI_REFRESH_SEC:
                self._aoi_t = time.time()
                self._resync_scene(clear=False)
        # ★ 传送回执超时提醒：服务端没回来，说明这条 0x407 被忽略了
        if self.in_world and self._pos_unconfirmed \
                and time.time() - self._pos_unconfirmed > 3.0:
            self._pos_unconfirmed = 0.0
            self.log('[!] 传送 3 秒内没收到服务端 0x62b 回执 —— 人可能还在原地，'
                     '界面上的距离会偏；换个 z 或换个点再传一次')
        # ★ 复活重试：死了才需要，依次试候选类型，收到 0x646 就停
        if self.in_world and self.dead and self._relive_pending \
                and time.time() - self.relive_last > 2.5:
            if self.relive_try >= len(self.RELIVE_TYPES):
                self._relive_pending = False
                self.log('[!] 三种复活类型都发过了，服务端没回 0x646 —— '
                         '可能得用「复活石」道具，或在客户端里手动点')
            else:
                try:
                    self._send_relive(self.RELIVE_TYPES[self.relive_try])
                    self.relive_try += 1
                    self.relive_last = time.time()
                except Exception as ex:
                    self._relive_pending = False
                    self.log('[!] 复活包发送失败：%s' % ex)
        # ★ 服务端自动战斗：续期 + 每 60 秒报一次现场
        if self.in_world and self.bot_on:
            _now = time.time()
            if _now - self.bot_last >= BOT_RENEW_SEC:
                self.bot_last = _now
                try:
                    self.w.sendall(wframe(0x4C7, BOT_RENEW))
                    self.log('   [打怪] 0x4c7 = 02 续期（服务端自动战斗 +600s）')
                except Exception as ex:
                    self.log('[!] 自动战斗续期失败：%s' % ex)
            if _now - self.bot_stat_t >= 60.0:
                self.bot_stat_t = _now
                ns = self._npc_list()
                if ns:
                    d, nm, _e = ns[0][0], ns[0][1], ns[0][2]
                    self.log('   [打怪] 附近存活 %d 个 · 最近 %s（%.1f m）· 累计倒下 %d'
                             % (len(ns), nm, d, self.bot_kills))
                else:
                    self.log('   [打怪] 附近没看到怪（已清空 / 实体未刷新）· 累计倒下 %d'
                             % self.bot_kills)
        # ★ 技能探测优先跑；探测期间不自动打怪，免得两套包打架
        if self.probe:
            self._probe_step()
        elif self.sweep:
            self._sweep_step()
        # ★ 自己打怪：自动挑最近的怪放技能
        elif self.in_world and self.auto_atk:
            self._auto_atk_step()
        # ★ 通用技能格（新版界面那 2 个框）：2026-10-20 按用户要求改成
        #   **纯手动** —— 点一下放一次，不自动循环放（原来的 _buff_step 已删）。
        # ★ 每 1 秒把怪物列表推给界面（哪怕没开自动打也刷，方便肉眼观察）
        if self.in_world and time.time() - self._npcs_t >= 1.0:
            self._npcs_t = time.time()
            # ★ 给界面的是 with_bl=True（排除了的怪也显示，方便取消排除）；
            #   打怪路径一律用默认（不含被排除的）。
            _lst = self._npc_list(with_bl=True)
            self.ev.put(('npcs', _lst))
            # 每 30 秒打一条现场，出问题时看这几行就知道卡在哪一层
            if time.time() - getattr(self, '_stat_t', 0.0) >= 30.0:
                self._stat_t = time.time()
                _wc = sum(1 for o in self.ent.values()
                          if o['x'] is not None or o['rawx'] is not None)
                _hit = [t for t in _lst if t[0] >= 0]
                _head = ('最近 %s %.1f m' % (_hit[0][1], _hit[0][0])
                         if _hit else '范围内没有怪')
                _nm = sum(1 for o in self.ent.values() if o.get('name'))
                self.log('   [现场] 台账 %d · 有坐标 %d · 有名 %d · 列表 %d · %s'
                         ' · 我在(%s) · 累计倒下 %d · 身份包 %d'
                         % (len(self.ent), _wc, _nm, len(_lst), _head,
                            ('%.0f,%.0f' % (self.pos[0], self.pos[1]))
                            if self.pos else '未知', self.bot_kills, self.n6b9))
        # ★ 身份到手但没有坐标的实体，补问一次 0x47e，赌服务端会回 0x647 带坐标
        if self.in_world and self.ent_pend:
            self._query_pending()
        # ★ 有坐标没名字的实体（新刷出来的怪）补查身份：
        #   不查就永远「未知」，界面看不懂、选目标也分不清怪和宠物
        if self.in_world:
            self._ident_retry()
        # 背包数据静默合并：距最后一帧 ≥0.4 秒才推一次完整的
        # （不能「来帧就推」，几十帧连发会刷爆；也不能「丢弃」，否则只剩第一帧）
        if self._bag_dirty and time.time() - self._bag_t >= 0.4:
            self._bag_push()
        # 进世界后补要一次背包数据（时间戳由 0x603 处理里设置，见那段注释）
        # 「用完为止」循环：每秒发一次使用包，直到背包里数量归零
        self._use_loop_tick()
        if self.in_world and self._bag_ask_t and time.time() >= self._bag_ask_t:
            self._bag_ask_t = 0.0
            try:
                self.w.sendall(wframe(0x411,
                                      b'\x76\x00\x00\x00\x00\x00\x00\x00'))
                self.log('   [背包] 补要一次背包数据（0x411）')
            except Exception:
                pass
            # 再等 5 秒，如果背包还是一帧都没收到 → 说明服务端根本没推，
            # 或者 0x411 不是"要背包"的包，得换思路（比如进世界前才有）
            self._bag_warn_t = time.time() + 5.0
        if (self.in_world and self._bag_warn_t
                and time.time() >= self._bag_warn_t):
            self._bag_warn_t = 0.0
            if not self.bag:
                self.log('[!] 背包一帧 0x613 都没收到 —— 服务端没推。'
                         '如果游戏里背包确实有东西，说明 0x411 请求无效，'
                         '需要在进世界那一刻抓包看服务端是何时下发的')
            elif not any(is_box_item(int(v.get('iid') or 0))
                         for v in self.bag.values()):
                self.log('   [背包] 收到 %d 个槽位，但都不是「箱子」类 —— '
                         '已先显示前几件（判定条件可按物品名调整）'
                         % len(self.bag))
        # 心跳（★ 2026-10-17 忠实还原真客户端 FUN_00519b20）
        #   正常每 1000ms 一发；若 3 秒内没收到 0x798 应答则立即补发
        #   payload = 4B u32 世界时钟，必须与服务端 0x71d 广播对齐
        if self.in_world:
            _now = time.time()
            _el = _now - self.last_hb
            _acked = self.hb_ack_t > self.last_hb
            if (_el >= 1.0 if _acked else _el >= 3.0):
                try:
                    hb = self.hb_now()
                    self.w.sendall(wframe(0x50F, struct.pack('<I', hb)))
                    self.hb_count += 1
                    self.last_hb = _now
                    if self.hb_count in (1, 2, 5, 10) or self.hb_count % 60 == 0:
                        self.log('   心跳 #%d（已在线 %d 秒）'
                                 % (self.hb_count, int(time.time() - self.t_inworld)))
                except Exception as ex:
                    self.log('[!] 心跳发送失败：%s' % ex)
                    self.logout('心跳失败')
        self.st_tick(inworld=self.in_world, hb=self.hb_count, nrecv=self.nrecv,
                     nframes=self.nframes, mapname=self.map_name, mapid=self.map_id,
                     pos=self.pos,
                     dur=(time.time() - self.t_inworld) if self.in_world else 0,
                     role=self.online_role['name'] if self.online_role else '')

    def _recv_once(self):
        if self.w is None:
            return
        try:
            self.w.settimeout(0.2)
            d = self.w.recv(65536)
            if not d:
                self.drop_world('World 连接被服务端关闭')
                return
            self.buf += d
            self.nrecv += 1
        except socket.timeout:
            pass
        except (ConnectionResetError, OSError) as ex:
            self.drop_world('World 连接异常（%s）' % type(ex).__name__)
            return
        # ★ BUGFIX 2026-10-21：解析/心跳单帧出错不能把整条连接流程打断
        try:
            self._parse_buf()
        except Exception as ex:
            self.log('[!] 拆包异常（已忽略）：%s' % ex)
        try:
            self._tick()
        except Exception as ex:
            self.log('[!] 心跳异常（已忽略）：%s' % ex)

    def pump(self, sec):
        """在 sec 秒内持续收包 + 处理心跳（不处理指令队列）"""
        t = time.time()
        while time.time() - t < sec and self.running and not self.abort:
            if self.w is not None:
                self._recv_once()
            else:
                time.sleep(0.04)

    def pump_until(self, cond, timeout, break_if_closed=False):
        t0 = time.time()
        while time.time() - t0 < timeout and self.running and not self.abort:
            if break_if_closed and self.w is None:
                break
            if self.w is not None:
                self._recv_once()
            else:
                time.sleep(0.04)
            if cond():
                return True
        return cond()

    # ---------------- ① 登录 + 大区/分区
    def _login_gate(self, acct):
        """多线程录入的登录闸门。返回 False = 被取消。

        ★★★ 2026-10-21 多线程录入的关键前提：
          以前录入是「全程序一条连接、换账号就 logout → login」，靠 3 秒固定
          冷却保证顺序。现在每条登录都是**独立线程 + 独立 socket**，多个线程
          可能同时往登录服打 —— 服务端会把这种突发判成异常连接直接拒
          （旧注释里"一个都登不上"就是这个原因）。
          所以这里统一排队：相邻两次真正开始连接至少隔 _LOGIN_MIN_GAP 秒，
          同一账号还要额外等 _ACCT_COOLDOWN 秒。等待用 pump()，能被 abort 打断。
        """
        _ac = (acct or '').strip()
        # ① 同账号冷却（上一个会话服务端还没清掉，连太快直接失败）
        if _ac:
            prev = _LOGIN_T_BY_ACCT.get(_ac, 0.0)
            if prev:
                d = _ACCT_COOLDOWN - (time.time() - prev)
                if d > 0.05:
                    self.log('[1] 同账号刚登录过，再等 %.1fs 让上个会话释放' % d)
                    self.pump(d)
                    if self.abort:
                        return False
        # ② 全局节流：领一个时间槽，到点再连（多线程同时登录也不会撞在一起）
        with _LOGIN_GATE:
            slot = max(time.time(), _LOGIN_LAST_T[0] + _LOGIN_MIN_GAP)
            _LOGIN_LAST_T[0] = slot
        d = slot - time.time()
        if d > 0.05:
            self.log('[1] 登录排队中（还要等 %.1fs）…' % d)
            self.pump(d)
            if self.abort:
                return False
        if _ac:
            _LOGIN_T_BY_ACCT[_ac] = time.time()
        return True

    def do_login(self, host, port, acct, pwd, silent=False):
        self._host, self._port = host, port
        self._acct, self._pwd = acct, pwd
        self.abort = False
        try:
            self.close_all()
            self.state = 'idle'
            # ★ 2026-10-21 多线程：原来是固定 sleep(3.0)，现在改成按账号 + 全局排队，
            #   不同账号之间互不拖累（见 _login_gate）。
            if self.rhythm:
                if not self._login_gate(acct):
                    return False
            self._stage = '连接登录服'
            self.log('[1] 正在连接登录服务器…')
            s = socket.create_connection((host, port), timeout=15)
            s.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
            s.settimeout(10)
            buf = bytearray()
            t0 = time.time()
            while time.time() - t0 < 8:
                d = s.recv(8192)
                if not d:
                    break
                buf += d
                if parse_frames(bytes(buf))[0]:
                    break
            fr = parse_frames(bytes(buf))[0]
            if not fr or fr[0][0] != 0x126:
                raise RuntimeError('首包不是 0x126（%s）' % bytes(buf[:12]).hex())
            n, e = der_pub(fr[0][2])
            self._stage = '取公钥'
            self.log('[1] 已取得加密公钥')

            tpl = bytearray(bytes.fromhex(LOGIN_TPL_HEX))
            ac = acct.encode()
            tpl[8:8 + len(ac)] = ac
            tpl[8 + len(ac)] = 0
            ctx = bytes(x ^ XOR_KEY for x in pkcs1_v15(n, e, pwd.encode()))
            tpl[4 + 0x45:4 + 0x45 + 64] = ctx
            tpl[4 + 0x85] = XOR_KEY
            tpl[4 + 568:4 + 570] = b'\x00\x00'
            tpl[4 + 570:4 + 572] = jg_cksum(bytes(tpl[4:4 + 568])).to_bytes(2, 'little')
            time.sleep(0.2)
            s.sendall(bytes(tpl))
            self._stage = '校验账号'
            self.log('[1] 正在校验账号「%s」…' % acct)

            r = s.recv(8192)
            res = None
            for c, f, pl in parse_frames(r)[0]:
                if c == 0x113:
                    res = pl
            if res is None:
                raise RuntimeError('未收到登录结果 0x113')
            # ★ 诊断用：留一份 0x113 原始载荷。对比不同账号时能看出服务端
            #   在登录那一刻就给这个账号打了什么标记（见 _probe_login.py）。
            self.last_113 = res
            # ★ 服务端在 @4..7 下发这个账号专属的魔数，World 侧全程要用它
            if len(res) >= 8:
                self.magic = bytes(res[4:8])
            if res[0] != 1:
                raise RuntimeError('登录失败（result=%d）：账号或密码错误' % res[0])
            self.token = res[8:12]
            # ★ 2026-10-21 排障：token 必须每个账号都不一样。
            #   如果第二次登录打出来的 token 和上一次相同，说明登录根本没换成新账号，
            #   后面连 World 用的是旧 token —— 服务端当然认为"那个账号还占着"。
            self.log('[1] 登录成功 ✓ 账号=%s token=%s'
                     % (acct, self.token.hex() if self.token else '?'))

            time.sleep(0.2)
            s.sendall(wframe(0x113, struct.pack('<I', 0x0865bbe8)))
            buf = bytearray()
            s.settimeout(0.4)
            t0 = time.time()
            while time.time() - t0 < 8:
                try:
                    d = s.recv(65536)
                    if not d:
                        break
                    buf += d
                except socket.timeout:
                    if buf:
                        break
            areas, lines = [], []
            for c, f, pl in parse_frames(bytes(buf))[0]:
                if c == 0x121:
                    areas.append({'id': struct.unpack('<I', pl[0:4])[0], 'name': gbk(pl[0x0F:])})
                elif c == 0x117:
                    lines.append({
                        'name': gbk(pl[0:0x16]),
                        'ip1': socket.inet_ntoa(pl[0x16:0x1A][::-1]),
                        'port1': struct.unpack('<H', pl[0x1A:0x1C])[0],
                        'ip2': socket.inet_ntoa(pl[0x1C:0x20][::-1]),
                        'port2': struct.unpack('<H', pl[0x20:0x22])[0],
                        'area': pl[0x22], 'line': pl[0x23]})
            if not areas and not lines:
                raise RuntimeError('未读到区服/线路列表')
            self.areas, self.lines = areas, lines
            self.ls = s
            self.state = 'logged'
            self._stage = '读区服列表'
            self.log('[1] 读取到 %d 个大区、%d 个分区 ✓' % (len(areas), len(lines)))
            if not silent:
                self.ev.put(('areas', areas))
                self.ev.put(('lines', lines))
                self.st(step='② 请选择大区 / 分区', logged=True)
            else:
                self.log('[1] （静默重登：界面选择保持不变）')
            return True
        except Exception as ex:
            self.log('[!] 登录失败：%s（阶段：%s）'
                     % (ex, getattr(self, '_stage', '?')))
            self.state = 'idle'
            self.err = str(ex)
            self.st(step='① 登录', logged=False)
            self.ev.put(('error', str(ex)))
            return False

    # ---------------- ② 连 World（读角色）
    def open_world(self, line):
        # ★ 服务端释放上一个 World 连接要点时间；太急着重连会被直接 RST。
        #   所以：刚刚有活连接 → 等满 4 秒；刚断过 → 补足到 4 秒；从没连过 → 不等。
        had = self.w is not None
        _ac = (getattr(self, '_acct', '') or '').strip()
        last_close = max(self._t_world_closed or 0.0,
                         _WORLD_CLOSE_BY_ACCT.get(_ac, 0.0) if _ac else 0.0)
        self.close_world()
        # 4.0 → 5.0：录入时「选角→退回→断开」之后马上重连，4 秒偶尔还不够
        wait = 5.0 if had else max(0.0, 5.0 - (time.time() - last_close))
        if wait > 0.3:
            self.log('[*] 等 %.1fs 让服务端释放上一个连接…' % wait)
            self.pump(wait)
        self.cur_line = line
        ip, port = line['ip1'], line['port1']
        self.log('[2] 正在连接分区「%s」…' % line['name'])
        self._pace(1.2)
        w = socket.create_connection((ip, port), timeout=10)
        w.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        self.w = w
        self.buf = bytearray()
        self.off = 0
        self.sent201 = self.sent202 = self.sent401 = self.sent4b0 = False
        self.last_cmds = []             # 诊断用：每连接从零开始记，别串上一次的
        self.roles = []
        self._roles_seen = set()
        self.roles_last_t = 0.0
        self.wlines = []
        self.in_world = False
        self.hb_count = 0
        self.nrecv = 0
        self.nframes = 0
        self.online_role = None
        self.picked_cid = None
        p207 = b'\x01\x00\x00\x00' + self.magic + b'\x00\x00\x00\x00' + self.token
        w.sendall(wframe(0x207, p207))
        self.log('[2] 已发送连接握手（账号=%s token=%s）'
                 % (getattr(self, '_acct', '?'),
                    self.token.hex() if self.token else '?'))
        self.state = 'world'
        self.st(step='④ 读取角色列表中…')

    # ---------------- ③ 选角（只为取线路表，不发 0x20f 就不会进世界）
    def pick_and_fetch_lines(self, role):
        if not role.get('cid'):
            raise RuntimeError('角色号解析失败：%s' % role['name'])
        # ★★★ 真客户端抓包结论（15:31 wire.jsonl）：
        #   一条 World 连接上想换角色，必须**先发 0x210（载荷 1 字节 0x24）退回角色选择界面**，
        #   然后才能再发 0x205 选另一个角色。少了 0x210 直接重发 0x205 会被服务端 RST。
        #   真客户端实测序列：0x205(角A) → 0x210/24 → 0x205(角B) → 0x20f
        #   注意：只要这条连接上**选过一次**，再选（哪怕还是同一个角色）都必须先发 0x210
        if self.picked_cid is not None:
            self._pace(0.6)
            self.w.sendall(wframe(0x210, b'\x24'))
            self.log('[3] 已退回角色选择界面')
            self.wlines = []
            self.ev.put(('wlines', []))
            self._pace(0.8)
        self.pick_role = role
        self.state = 'roles'            # 重置，好等这一次新的 0x213
        self._pace(1.2)
        sel = (b'\x01\x00\x00\x00' + self.magic +
               struct.pack('<I', role['cid']) + b'\x00')
        self.w.sendall(wframe(0x205, sel))
        self.picked_cid = role['cid']
        self.log('[3] 已选择角色：%s' % role['name'])
        self.st(step='⑤ 读取线路中…')
        if not self.pump_until(lambda: self.state == 'wlines', 4,
                               break_if_closed=True):
            if self.abort:
                return False
            if self.w is None:
                raise RuntimeError('连接被服务端关闭（选角被拒）')
            # ★★★ 2026-10-21 单线路区：用户实测「天王琴」这种区只有一条线，
            #   服务端**压根不发 0x213 线路表**（不是慢，是没有）。
            #   以前在这里死等 15 秒然后报「未收到线路表」，那个角色永远上不去。
            #   现在：等 4 秒没来就当作单线路区，wlines 留空，由 do_enter 用
            #   默认值（v1=0/v2=0）继续发 0x20F → 0x401。
            #   正常多线路区 0x213 通常 1 秒内就到，4 秒足够，不会误判。
            self.wlines = []
            self.ev.put(('wlines', []))
            self.log('[*] 这个分区没有线路表（单线路区）—— 直接进世界，不用选线')
            return True
        return True

    # ---------------- ④ 点选角色 → 读线路表（不进世界）
    def do_pick_lines(self, role):
        """发 0x205 选角 → 收 0x213 线路表。
        不发 0x20f，所以只"读线路"，不会进世界。
        ★ 服务端一条 World 连接只允许选一次角色，所以 picked_cid 只能设一次。"""
        self.abort = False
        try:
            if self.w is None or not self.roles:
                raise RuntimeError('请先选择分区（先把角色读出来）')
            if self.in_world:
                raise RuntimeError('角色已在线，请先「批量下线」')
            if role is None:
                raise RuntimeError('请先点选一个角色')
            if self.picked_cid == role.get('cid') and self.wlines:
                self.ev.put(('wlines', list(self.wlines)))
                self.st(step='⑥ 请选择线路 → 点「进入游戏」')
                return
            if not self.pick_and_fetch_lines(role):
                return
            self.st(step='⑥ 请选择线路 → 点「进入游戏」')
        except Exception as ex:
            self.log('[!] 读取线路失败：%s' % ex)
            self.err = str(ex)
            self.ev.put(('error', str(ex)))
            self.st(step='读取线路失败')

    # ---------------- ⑤ 连 World 读角色（不选角、不进世界）
    def do_load_roles(self, line, _try=0):
        """只连 World 把角色列表读出来。
        不选角、不读线路 —— 选角要等用户点选角色时再做（一条连接只能选一次）。"""
        self.abort = False
        try:
            if self.ls is None:
                raise RuntimeError('请先登录账号')
            if (self.w is not None and self.cur_line is line and self.roles):
                self.ev.put(('roles', list(self.roles)))
                if self.wlines:
                    self.ev.put(('wlines', list(self.wlines)))
                self.st(step='④ 请点选一个角色')
                return
            self.open_world(line)
            if not self.pump_until(lambda: self.state == 'roles', 20,
                                   break_if_closed=True):
                if self.abort:
                    return
                if self.w is None:
                    # ★★★ 2026-10-21 不自动重试了。
                    #   服务端对同 IP 的连接频率有限制，失败后 3 秒就重连会把
                    #   我们直接送进限流（实测 12:45 连登录服都回 10054）。
                    #   读角色本来就是**可选**动作：读不到就在左边手填角色名，
                    #   照样能录入、能上线。
                    raise RuntimeError('分区服务器把连接关了 —— 读不到角色列表。'
                                       '**直接在左边「角色名」里手填名字就能录入**，'
                                       '不用非得读角色。'
                                       '（服务端可能正在限流，等 5~10 分钟再点「读角色」）')
                raise RuntimeError('读取角色超时（World 握手无响应）')
            self.ev.put(('roles', list(self.roles)))
            self.st(step='④ 请点选一个角色')
        except Exception as ex:
            _cmds = ' '.join('0x%04X(%dB)' % (c, n) for c, n in
                             (getattr(self, 'last_cmds', []) or [])[-8:])
            self.log('[!] 读取角色失败：%s' % ex)
            self.log('   [诊断] World 收到 %d 字节 / %d 帧'
                     % (getattr(self, 'nrecv', 0), getattr(self, 'nframes', 0)))
            self.log('   [诊断] 服务端最后发来的帧：%s' % (_cmds or '一帧都没有'))
            self.log('   [诊断] 本次握手用的 token：%s'
                     % (self.token.hex() if self.token else '?'))
            self.log('   → 读不到也没关系：左边「角色名」手填一样能录入')
            self.err = str(ex)
            self.ev.put(('error', str(ex)))
            self.st(step='读取角色失败')

    # ---------------- ⑤ 一键进入（读角色 → 选角 → 进世界）
    def do_enter(self, line, role_id=None, wline_i=0, char_idx=None,
                 role_name=None, wline_name=None, _try=0):
        """line=分区(0x117)；role_id=目标角色数字ID（None→按名字找→再不行第一个）；
        wline_i=大世界线路序号（0 起）；char_idx=0x20f 里带的角色序号（不传则用 0）

        ★ 2026-10-21 多开/录入：新增 role_name / wline_name。
          「一键上线」拿到的是档案里存的名字（角色名、线路名），读回列表后
          按名字精确匹配 —— 服务端的 role_id / 线路序号每次可能变，名字最稳。
        """
        self.abort = False
        self._char_idx = char_idx
        try:
            if self.state == 'idle' or self.ls is None:
                raise RuntimeError('请先登录账号')
            # ★ 换线/重新进入：若已有角色在线，必须先断开 World 再重连，
            #   否则会在"已进世界"的连接上再发选角包，服务端不认 → 换线无效。
            if self.in_world:
                self.log('[*] 当前已有角色在线 —— 先断开，再重新进入')
                self.close_world()
            need = (self.w is None) or (self.cur_line is not line) or (not self.roles)
            if need:
                self.open_world(line)
                if not self.pump_until(lambda: self.state == 'roles', 20,
                                       break_if_closed=True):
                    if self.abort:
                        return
                    if self.w is None:
                        # ★★★ 2026-10-21 不再自动重试（原因同 do_load_roles）：
                        #   自动重连会把自己送进服务端限流，越试越连不上。
                        raise RuntimeError('连接被服务端关闭（该账号的 World 还没释放，'
                                           '或本机 IP 正在被限流）—— **别再连续点了**，'
                                           '等 5~10 分钟再点一次「上线」')
                    raise RuntimeError('未读到角色列表（World 握手失败）')
            if not self.roles:
                raise RuntimeError('该分区下没有角色')

            role = None
            if role_id is not None:
                for r in self.roles:
                    if r['id'] == role_id:
                        role = r; break
            if role is None and role_name:
                # 档案里存的是名字：先精确，再退「包含」（防止前后空格/后缀差异）
                _want = str(role_name).strip()
                for r in self.roles:
                    if (r.get('name') or '').strip() == _want:
                        role = r; break
                if role is None:
                    for r in self.roles:
                        if _want and _want in (r.get('name') or ''):
                            role = r; break
                if role is not None:
                    self.log('[3] 按名字匹配到角色「%s」' % role['name'])
            if role is None:
                role = self.roles[0]
            if not role.get('cid'):
                raise RuntimeError('角色号解析失败，请重新读取角色（角色：%s）' % role['name'])

            # 已经为这个角色选过角、且线路表还在 → 直接进世界，不用再选一次
            self.pick_role = role
            if self.picked_cid != role['cid'] or not self.wlines:
                self.ev.put(('pick', role))
                if not self.pick_and_fetch_lines(role):
                    return
            if not self.wlines:
                # ★ 单线路区（服务端不发 0x213）：没有线路可选，用默认参数继续。
                #   v1=地图ID、v2=线路号；这里都填 0，让服务端自己分配。
                self.log('[*] 无线路表 —— 用默认参数进世界（地图/线路=0）')
                self.pick_wline = {'name': '默认线路', 'v1': 0, 'v2': 0, 'ip': ''}
                self.ev.put(('wline_sel', 0))
            else:
                i = None
                if wline_name:
                    _w = str(wline_name).strip()
                    for k, wl in enumerate(self.wlines):
                        if (wl.get('name') or '').strip() == _w:
                            i = k; break
                    if i is None:
                        for k, wl in enumerate(self.wlines):
                            if _w and _w in (wl.get('name') or ''):
                                i = k; break
                if i is None:
                    i = wline_i if 0 <= wline_i < len(self.wlines) else 0
                self.pick_wline = self.wlines[i]
                self.ev.put(('wline_sel', i))
            self._pace(1.0)
            # ★ 0x20f 的 4 字节：疑似"角色序号"（默认 0 = 第一个角色）
            ci = self._char_idx if self._char_idx is not None else 0
            self.w.sendall(wframe(0x20F, struct.pack('<I', ci & 0xFFFFFFFF)))
            self.log('[4] 正在进入游戏（线路：%s）' % self.pick_wline['name'])
            self.st(step='⑦ 进入世界中…')
            # ★ 单线路区兜底：这类区可能连 0x214 都不发。等 3 秒还没有进线
            #   请求发出，就自己发 0x401（地图/线路填 0，让服务端分配）。
            if not self.wlines:
                self.pump(3.0)
                if not self.abort and not self.sent401 and not self.in_world:
                    self.log('   （没等到 0x214 —— 主动发进线请求）')
                    self._send_401()
            if not self.pump_until(lambda: self.in_world, 25, break_if_closed=True):
                if self.abort:
                    return
                if self.w is None:
                    raise RuntimeError('连接被服务端关闭（进入世界被拒）')
                raise RuntimeError('进入世界超时（未收到 0x603）')
            self.log('   ★★「%s」已进入游戏' % role['name'])
            self.ev.put(('online', role))
        except Exception as ex:
            self.log('[!] 进入游戏失败：%s' % ex)
            self.err = str(ex)
            self.ev.put(('error', str(ex)))
            self.st(step='进入失败')

    # ---------------- 收包处理
    def _send_401(self):
        """发 0x401 + 0x43E 请求进线路。两个时机都走这里：
          ① 正常多线路区：收到 0x214 之后
          ② 单线路区：服务端既不发 0x213 也不发 0x214，由 do_enter 兜底主动发
        """
        if self.sent401 or self.pick_wline is None or self.w is None:
            return
        self.sent401 = True
        wl = self.pick_wline
        _v1 = int(wl.get('v1') or 0)
        _v2 = int(wl.get('v2') or 0)
        tick = int(time.time() * 1000) & 0xFFFFFFFF
        p401 = (b'\x01\x00\x00\x00' + self.magic +
                struct.pack('<I', _v1) + struct.pack('<I', _v2) +
                self.token + b'\x69\x00\x00\x00' + b'\x69\x00\x00\x00' +
                struct.pack('<I', tick))
        try:
            self.w.sendall(wframe(0x401, p401))
            self.w.sendall(wframe(0x43E, b'\x40\x00\x00\x00'))
            self.log('   → 已请求进入线路（地图=%d 线路=%d）' % (_v1, _v2))
        except Exception as ex:
            self.log('[!] 发进线请求失败：%s' % ex)

    def handle_frame(self, cmd, pl):
        self.nframes += 1
        try:
            self.last_cmds.append((cmd, len(pl)))
            if len(self.last_cmds) > 16:
                del self.last_cmds[:-16]
        except Exception:
            pass
        if self.dump_rx:
            self._dump_frame(cmd, pl)
        if cmd == 0x3001:
            self.log('   服务端已响应')
        elif cmd == 0x20C:
            # ★★★★ 2026-10-21 定案：**只回第一次**，与 脱机进世界.py 完全一致。
            #   之前（v3.3）改成"每次都回 0x201"，依据是 12:06 日志里看到服务端
            #   连发两次 0x20C、只回一次就不下发角色列表。但那次实验用的是
            #   **f6 魔数**（错误的那版），服务端本来就在拒绝 —— 结论是误判。
            #   12:26 的日志已经证明：f6 下服务端回 0x20C **flag=1**，3 秒 RST。
            #   现在魔数回退成 f3，按实测脚本的行为只回第一次。
            #   flag 仍打出来：0 = 放行；非 0 = 服务端真的拒绝（那时候回什么都没用）。
            _flag = pl[0] if pl else -1
            if self.sent201:
                self.log('   [握手] 又收到 0x20C（flag=%d）—— 已回过 0x201，不重复回'
                         % _flag)
            else:
                if _flag not in (0, -1):
                    self.log('[!] 握手被服务端拒绝（flag=%d）—— 多半是该账号还有别的'
                             '会话（游戏客户端/启动器）占着' % _flag)
                self.log('   [握手] 0x20C（flag=%d）→ 回 0x201' % _flag)
                try:
                    self._micro(0.06, 0.2)
                    self.w.sendall(wframe(0x201, b'\x01\x00\x00\x00' +
                                          self.magic + b'\x00\x00\x00\x00'))
                    self.sent201 = True
                except Exception as _ex:
                    self.log('[!] 回 0x201 失败：%s' % _ex)
        elif cmd == 0x203:
            # 同样只回一次（与实测脚本一致）
            if not self.sent202:
                try:
                    self._micro(0.06, 0.2)
                    self.w.sendall(wframe(0x202, b'\x01\x00\x00\x00' +
                                          self.magic + b'\x00\x72\x65\x61'))
                    self.sent202 = True
                except Exception:
                    pass
        # ================= 组队：邀请 / 申请 / 合并 的自动同意 =================
        # ★★★ 2026-10-21 实测定案（录制 20261021_142646 与 20261021_144134 双场一致）
        #   这三类"确认请求"是**结构化二进制包**，不是中文文本消息，所以按
        #   "邀请您加入队伍"搜关键字永远搜不到 —— 之前 4 次录制都以为没录到，
        #   实际第一次就录到了，只是找错了地方。
        #
        #   0x684 TeamInviteAddConfirm  别人邀请我入队    → 回 0x456 TeamInviteAddConfirmRet
        #   0x685 TeamApplyAddConfirm   别人申请加入我的队 → 回 0x457 TeamApplyAddConfirmRet
        #   0x686 TeamUnitConfirm       队伍合并确认      → 回 0x458 TeamUnitConfirmRet
        #
        #   实测 0x684 载荷（43 字节，两场只差时间戳/坐标）：
        #     [0:4]  发起者 cid   2105 = 佐菲
        #     [4:8]  自己 cid     1835
        #     [8:12] 时间戳
        #     [12:..] 发起者名字  GBK "佐菲"
        #   实测 0x456 载荷（11 字节）= 0x684 的 [0:8] 原样回填 + 01 00 00
        #     （两场分别回 010100 / 010000，第 9 字节恒为 01 = 同意，
        #       第 10 字节 01/00 都成功过，取 00）
        #   → 所以完全不用猜字段含义：把收到的前 8 字节原样回填 + 010000 就成立。
        elif cmd in (0x684, 0x685, 0x686) and len(pl) >= 8:
            _ret = {0x684: 0x456, 0x685: 0x457, 0x686: 0x458}[cmd]
            _kind = {0x684: '邀请你入队', 0x685: '申请加入你的队伍',
                     0x686: '请求队伍合并'}[cmd]
            _who, _me = struct.unpack('<II', pl[:8])
            _nm = ''
            try:
                _seg = pl[12:40].split(b'\x00')[0]
                if _seg:
                    _nm = _seg.decode('gbk', 'ignore')
            except Exception:
                pass
            _desc = ('「%s」cid=%d %s' % (_nm, _who, _kind) if _nm
                     else 'cid=%d %s' % (_who, _kind))
            if not self.auto_team:
                self.log('[队伍] %s —— 自动同意没开，已忽略' % _desc)
            elif self.w is None:
                self.log('[队伍] %s —— 连接不在世界，无法应答' % _desc)
            else:
                try:
                    self._micro(0.05, 0.15)
                    self.w.sendall(wframe(_ret, pl[:8] + b'\x01\x00\x00'))
                    self._team_auto_n += 1
                    self.log('   → 已自动同意：%s（回 0x%X）' % (_desc, _ret))
                except Exception as _ex:
                    self.log('[!] 自动同意失败（%s）：%s' % (_kind, _ex))
        elif cmd == 0x68E and len(pl) >= 24:
            # 队伍成员同步（每次队友进出/状态变化都会推）。这里只记 cid 到
            # self.team_mates，供界面上显示"队伍里几个人"。
            try:
                _cid = struct.unpack('<I', pl[16:20])[0]
                if _cid and _cid not in self.team_mates:
                    self.team_mates.append(_cid)
                    self.ev.put(('team', list(self.team_mates)))
            except Exception:
                pass
        elif cmd in (0x68F, 0x69A):
            # 0x68F TeamFreed（队伍解散）/ 0x69A TeamEnd（队伍结束）
            if self.team_mates:
                self.team_mates = []
                self.ev.put(('team', []))
                self.log('[队伍] 队伍已结束')
        # ================= 队长召唤：0x734 → 0x4CD =================
        #   协议名（来自 _namecache.json / protocol_full.txt）：
        #     s_nSC_TeamLeaderCallMember   0x734  服务端→客户端（弹窗"队长召唤你"）
        #     s_nCS_TeamMemberAcceptCall   0x4CD  客户端→服务端（点"确定"）
        #     s_nCS_TeamMemberIgnoreCall   0x4CE  客户端→服务端（点"取消"）
        #   注意 0x4CD / 0x4CE 是**两条不同命令**，不像 0x456 那样用布尔位区分
        #   同意/拒绝，所以应答载荷里应该不需要 01 标志。
        #
        #   ⚠ 载荷结构尚未实证（17 场历史录制里一次都没出现过 0x734）。
        #     当前按「与组队邀请同构」的假设先发 pl[:8]（队长cid + 自己cid），
        #     同时把 0x734 的完整 hex 打进日志 —— 万一不对，日志里就有真实数据，
        #     录一次包就能定死。
        elif cmd == 0x734:
            _hex = pl.hex()
            self.log('[队伍] 队长召唤（0x734 %dB）：%s' % (len(pl), _hex))
            if not self.auto_team:
                self.log('   自动同意没开 —— 已忽略（想自动接受请勾上「自动同意组队/召唤」）')
            elif self.w is None:
                self.log('   连接不在世界，无法应答')
            else:
                _body = pl[:8] if len(pl) >= 8 else pl
                try:
                    self._micro(0.05, 0.15)
                    self.w.sendall(wframe(0x4CD, _body))
                    self._team_auto_n += 1
                    self.log('   → 已自动接受召唤（0x4CD %dB）：%s'
                             % (len(_body), _body.hex()))
                except Exception as _ex:
                    self.log('[!] 自动接受召唤失败：%s' % _ex)
        elif cmd == 0x205 and len(pl) > 0x30:
            # ★ 实测：服务端对每个角色发一帧 0x205，必须累加去重
            added = []
            for r in roles_from_205(pl):
                if r['id'] not in self._roles_seen:
                    self._roles_seen.add(r['id'])
                    self.roles.append(r)
                    added.append(r)
            self.roles_last_t = time.time()
            for r in added:
                self.log('   发现角色：%s' % r['name'])
            if added:
                pass
            self.ev.put(('roles', list(self.roles)))
        elif cmd == 0x204:
            pass
        elif cmd == 0x213:
            self.wlines = worldlines_from_213(pl)
            self.log('   线路读取完成：%d 条' % len(self.wlines))
            for wl in self.wlines:
                self.log('       %s' % wl['name'])
            self.ev.put(('wlines', self.wlines))
            self.state = 'wlines'
            self.st(step='⑤ 线路已就绪')
        elif cmd == 0x214:
            if not self.sent401 and self.pick_wline:
                self._pace(2.0)
                self._send_401()
        elif cmd == 0x6E2:
            if not self.sent4b0:
                self.sent4b0 = True
                self._pace(2.0)
                mac = uuid.getnode().to_bytes(6, 'big')
                self.w.sendall(wframe(0x4B0, mac))
                self.log('   → 已上报设备信息')
        elif cmd == 0x66C and len(pl) >= 10:
            self.map_id = struct.unpack('<I', pl[4:8])[0]
            self.map_name = gbk(pl[8:])
        elif cmd == 0x603:
            self.in_world = True
            self.t_inworld = time.time()
            self.last_hb = time.time()
            self.state = 'inworld'
            self.online_role = self.pick_role
            if len(pl) >= 0x230:
                mid = struct.unpack('<I', pl[0x212:0x216])[0]
                nlen = struct.unpack('<H', pl[0x216:0x218])[0]
                nm = gbk(pl[0x218:0x218 + nlen]) if 0 < nlen < 64 else ''
                if nm:
                    self.map_id, self.map_name = mid, nm
            if len(pl) >= 0x54:
                x = int.from_bytes(pl[0x49:0x4C], 'little') / 100.0
                y = int.from_bytes(pl[0x4D:0x50], 'little') / 100.0
                z = int.from_bytes(pl[0x51:0x54], 'little') / 100.0
                if 0 < x < 20000 and 0 < y < 20000:
                    self.pos = (x, y, z)
            self.log('   ★★ 进入游戏成功，开始在线挂机')
            self.log('   ★ 心跳保活已启动')
            # ★ 收到 0x603 立刻排场景序列（真客户端 0.5 秒内发完，晚了等于没发）
            self.scene = {'seq': None, 'i': 0, 'done': False, 't0': time.time()}
            self.aoi_hs = False
            self.ent.clear()
            self.ent_seen.clear()
            self.ent_pend = []
            self.ent_queried.clear()
            self.rp_npc.clear()
            self.rp_tc.clear()
            self.rp_stat.clear()
            self.rp_pl.clear()
            self.rp_req.clear()
            self.my_cls = 0
            # 换场景 = 全新一批怪，旧的「打不动先跳过」记录跟着作废
            self._skip_t.clear()
            self._tgt_fail.clear()
            self._nofind_t = 0.0
            self._aoi_t = 0.0
            self._aoi_n = 0
            self.log('   → 已排入场景序列（激活角色 / AOI 握手 / 实体申报）')

            # ★ 2026-10-21：进世界后补要一次背包（0x411 8 字节，录制里客户端进世界
            #   后真实发过）。0x613 是服务端**一次性**推的，万一漏了、或被场景序列
            #   的初始化包挤掉，界面上的箱子格子就会一直空着。
            #   只记时间戳，真正发包放到 _tick（同一个线程里发，跨线程 sendall 会打架）。
            self._bag_ask_t = time.time() + 1.5
            self.st(step='⑧ 在线挂机中', inworld=True)
        # ======================= 世界交互层（站桩打怪的基础）=======================
        elif cmd == 0x647 and len(pl) >= 8:
            # ★★★ 实体清单：纯脱机拿「怪名 + 坐标」的唯一来源
            _b4 = set(self.ent.keys())
            n = self._parse_647(pl)
            _new = set(self.ent.keys()) - _b4
            # ⚠ 开了定时刷新之后 0x647 每 8 秒来一次，逐条打日志会刷屏。
            #   只在「数量变了」或「有新的实体出现」时才念一句 —— 后者正是
            #   「怪刷新出来了」的证据，值得看一眼。
            if n and (n != getattr(self, '_647_n', -1) or _new):
                self.log('   实体清单 0x647：解析出 %d 个（新出现 %d 个）'
                         % (n, len(_new)))
            self._647_n = n
            # 申报：NPC 回 0x46e，Tc 场景物件回 0x474。不回 → 服务端认为场景没加载完
            for k in range(0, len(pl) - 3):
                v = struct.unpack('<I', pl[k:k + 4])[0]
                if EID_NPC_LO <= v <= EID_NPC_HI:
                    if v not in self.rp_npc:
                        self.rp_npc.add(v)
                        try:
                            self.w.sendall(wframe(0x46E, struct.pack('<I', v)))
                        except Exception:
                            pass
                    if v not in self.ent_seen:
                        self.ent_seen.add(v)
                        self.ent_pend.append(v)
                elif EID_TC_LO <= v <= EID_TC_HI and v not in self.rp_tc:
                    self.rp_tc.add(v)
                    try:
                        self.w.sendall(wframe(0x474, struct.pack('<I', v)))
                    except Exception:
                        pass
            self._query_pending()
        elif cmd in (0x674, 0x6BC, 0x6B5) and len(pl) >= 4:
            # Tc 场景物件出现 → 回 0x474
            v = struct.unpack('<I', pl[:4])[0]
            if EID_TC_LO <= v <= EID_TC_HI and v not in self.rp_tc:
                self.rp_tc.add(v)
                try:
                    self.w.sendall(wframe(0x474, struct.pack('<I', v)))
                except Exception:
                    pass
        elif cmd == 0x6B9 and len(pl) == 141:
            # ★★★ s_nSC_Compact_NpcAppear —— **身份 + 坐标**
            #   [0x00] u32 实体ID
            #   [0x09] u16 X 定点（=(x*16+8) 低 16 位）
            #   [0x0B] u16 Y 定点（=(y*16+8) 低 13 位，周期 512 米）
            #   [0x23] u32 MNID（模板号）  ← 真录制 165/165 全部命中
            eid = struct.unpack('<I', pl[0:4])[0]
            mnid = struct.unpack('<I', pl[35:39])[0]
            self.n6b9 += 1
            inf = self._fill_ident(eid, mnid)
            # ★ 坐标就在这里。用自己位置反推圈数，解出来的距离精确到 0.00 米
            #   （15 个已知坐标实体逐条验证过）。
            #   ⚠ 0x6B9 常常比自己位置先到，所以这里只存原始定点值，
            #     真正换算放到 _npc_list 里做（那时自己位置肯定有了，
            #     传送之后再解一次也自动跟着走）。
            if EID_NPC_LO <= eid <= EID_NPC_HI:
                ux = struct.unpack('<H', pl[9:11])[0]
                uy = struct.unpack('<H', pl[11:13])[0]
                if ux or uy:
                    o = self._ent(eid)
                    o['rawx'], o['rawy'] = ux, uy
            if self._6b9_log < 8:
                self._6b9_log += 1
                self.log('   实体身份 0x6B9：0x%08x MNID=%d → %s'
                         % (eid, mnid,
                            ('%s lv%s %s [%s]' % inf) if inf else '表里没有'))
            # 收到身份数据 → 回 Stat 16B 告诉服务端「已入库」
            if eid and eid not in self.rp_stat:
                self.rp_stat.add(eid)
                try:
                    self.w.sendall(wframe(0x46F,
                                          struct.pack('<I', eid) + b'\x00' * 12))
                except Exception:
                    pass
        elif cmd == 0x6B9:
            # 0x6B9 还有 9 / 21 / 31 字节的变体（真录制里都有），不是身份包，
            # 这里只计数，用来判断「服务端到底有没有在推身份」
            self.n6b9o += 1
        elif cmd in (0x6B1, 0x6B2, 0x6B3, 0x6B4, 0x6B8, 0x6BA, 0x6BB) \
                and len(pl) >= 4:
            # 实体出现通知（只带实体ID）。★ 关键：
            #   本地还没有这个实体 → 必须回 **Req(4B)** 向服务端要详情，
            #   服务端才会下发 0x6B9（身份）。以前一律回 Stat(16B 全零)，
            #   等于跟服务端说「我早就有了」，于是怪物身份永远收不到。
            eid = struct.unpack('<I', pl[:4])[0]
            req = {0x6B1: 0x46C, 0x6B8: 0x46C,      # PlayerAppear_Req
                   0x6B2: 0x46E, 0x6BA: 0x46E,      # NpcAppear_Req
                   0x6B3: 0x470,                    # MbAppear_Req
                   0x6B4: 0x472, 0x6BB: 0x472}[cmd]  # TpAppear_Req
            stat = {0x6B1: 0x46D, 0x6B8: 0x46D, 0x6B2: 0x46F, 0x6BA: 0x46F,
                    0x6B3: 0x471, 0x6B4: 0x473, 0x6BB: 0x473}[cmd]
            if eid and eid not in self.rp_stat:
                self.rp_stat.add(eid)
                # ★ 判断依据是「有没有拿到身份」，不是「台账里有没有这条」。
                #   0x6D3/0x6D4 可能先到（只有坐标、没名字），这时台账里有它，
                #   但身份还没有 —— 以前就误判成"我有了"，于是永远拿不到 0x6B9，
                #   列表里全是一串 0x02625cad 这种没名字的。
                o = self.ent.get(eid)
                has_id = bool(o and (o.get('mnid') or o.get('name')))
                try:
                    if has_id:
                        self.w.sendall(wframe(stat, struct.pack('<I', eid) +
                                              b'\x00' * 12))
                    else:
                        self.w.sendall(wframe(req, struct.pack('<I', eid)))
                except Exception:
                    pass
        elif cmd == 0x6D4 and len(pl) == 10:
            # s_nSC_StopMove: [u32 实体ID][u16 X][u16 Y][u16 Z]（÷12.5 得世界坐标）
            self._setpos(struct.unpack('<I', pl[0:4])[0],
                         *struct.unpack('<HHH', pl[4:10]))
        elif cmd == 0x6D3 and len(pl) == 15:
            # s_nSC_StartMove: [eid][fromX][fromY][Z][toX][toY][u8 模式]
            # ★ 必须取 **from**（起点）：它才是「此刻站在哪」。
            #   取 to 的话，一只正走向 30 米外的怪会立刻显示在 30 米外，
            #   人明明贴着它，列表却写 30 多米 —— 之前就是错在这。
            eid = struct.unpack('<I', pl[0:4])[0]
            fx, fy, fz, _tx, _ty = struct.unpack('<HHHHH', pl[4:14])
            self._setpos(eid, fx, fy, fz)
            o = self.ent.get(eid)
            if o is not None:
                o['goal'] = (_tx / COORD_SCALE, _ty / COORD_SCALE)
        elif cmd == 0x6D4 or cmd == 0x6D3:
            pass                                     # 长度不认识的先忽略
        elif cmd == 0x608 and len(pl) >= 4:
            # s_nSC_RemoveCharacter → 实体离场，从台账删掉
            eid = struct.unpack('<I', pl[:4])[0]
            self.ent.pop(eid, None)
            self.rp_stat.discard(eid)
        elif cmd == 0x606 and len(pl) >= 8:
            eid = struct.unpack('<I', pl[4:8])[0]
            if 0 < eid < 0x10000:
                self._sub_player(eid)
        elif cmd == 0x62B and len(pl) >= 16:
            # s_nSC_ForceSetPosition: [u32 实体ID][f32 x][f32 y][f32 z]
            # ★ 第 0~3 字节是实体 ID，不是时间；别人的位置也走这个包
            eid = struct.unpack('<I', pl[:4])[0]
            x, y, z = struct.unpack('<fff', pl[4:16])
            if 0 < x < 20000 and 0 < y < 20000:
                me = self.picked_cid or 0
                if me and eid == me:
                    # ★ 服务端权威回写：这才算真的到位了
                    if self._pos_unconfirmed:
                        d = ((x - self.pos[0]) ** 2 + (y - self.pos[1]) ** 2) ** 0.5 \
                            if self.pos else 0.0
                        self._pos_unconfirmed = 0.0
                        self.log('   ✓ 服务端确认位置 0x62b：(%.1f, %.1f, %.1f)'
                                 ' 与目标差 %.1f m' % (x, y, z, d))
                    self.pos = (x, y, z)
                elif EID_NPC_LO <= eid <= EID_NPC_HI:
                    # 只收 NPC 段的，玩家/宠物不进打怪台账
                    o = self._ent(eid)
                    o['x'], o['y'], o['z'] = x, y, z
                    o['t'] = time.time()
        elif cmd == 0x613 and len(pl) >= 12:
            # s_nSC_PlayerItemOperation —— 背包槽位数据
            #   结构见 Client.__init__ 里 self.bag 那段注释（112B 实测）。
            #
            # ★★ 2026-10-21 第二次修（用户截图里只填了 1 格、显示 #222）：
            #   原来这里硬要求 `pl[1] == 1`（主背包），其余容器的帧直接丢弃 ——
            #   万一真机上的容器号和录制里不一样（1 是录制那个号的情况），
            #   就会只剩零星几帧进得来。现在**不再按容器号拦**，全都存进
            #   self.bag（键带上容器），推送时再按「容器 1 优先」排序，
            #   这样容器号猜错也能显示出东西。
            #
            #   同时把前 8 帧的原始 hex 打进日志：只有它能在下次一眼定案
            #   （字段偏移对不对、容器是几、物品 ID 到底在不在 [8:10]）。
            if len(pl) >= 12 and self._bag_dump < 8:
                self._bag_dump += 1
                self.log('   [背包] 0x613 原始 %dB：%s'
                         % (len(pl), pl[:28].hex()))
            if pl[0] == 3 and len(pl) >= 112:
                _cont = pl[1]
                _slot = struct.unpack_from('<H', pl, 2)[0]
                _iid = struct.unpack_from('<H', pl, 8)[0]
                _n = struct.unpack_from('<H', pl, 10)[0]
                if _iid:
                    self.bag[(_cont, _slot)] = {'iid': _iid, 'n': _n}
                    self._bag_seen += 1
                    # ★★ 只打标记，不当场推（见 _bag_push 上面那段「节流 bug」）
                    self._bag_dirty = True
                    self._bag_t = time.time()
                    if self._bag_seen <= 3 or self._bag_seen % 30 == 0:
                        self.log('   [背包] 收到 容器%d 槽位%d 物品%d 数量%d'
                                 '（累计 %d 条）'
                                 % (_cont, _slot, _iid, _n, len(self.bag)))
        elif cmd == 0x60F and len(pl) >= 24:
            # s_nSC_PlayerExpUpdate —— 等级 / 经验
            # ★★★ 2026-10-21 真机对照定案（角色 1624，用户报 574626/938220）：
            #   载荷里 [16:20] / [20:24] 是 **×256 的定点数**：
            #     147321856 / 256 = 575476  ← 与 0x623 attr 3009 同值
            #     240184320 / 256 = 938220  ← 与角色面板「升级所需」完全一致
            #   所以必须右移 8 位（不是直接当整数用）。
            _cid = struct.unpack_from('<I', pl, 0)[0]
            _lv = pl[4]
            _exp = struct.unpack_from('<I', pl, 16)[0] >> 8
            _need = struct.unpack_from('<I', pl, 20)[0] >> 8
            self._note_lv(_cid, _lv, _exp, _need)
        elif cmd == 0x624 and len(pl) >= 58:
            # ★★★ s_nSC_PlayerAttr —— 自身属性全量（98 字节，进世界时下发）
            #   2026-10-21 真机对照（用户报 血 853/1285、蓝 689/1017）：
            #     [0:4]  cid
            #     u16@38 当前血量 853     u16@42 当前法力 689
            #     u16@50 血量上限 1285    u16@54 法力上限 1017
            #   ⚠ 血/蓝上限以前只能等 0x623 的 2008/2009，而实测**根本不发**，
            #     所以血条没有分母、蓝条整个是空的。这里才是正源。
            _c = struct.unpack_from('<I', pl, 0)[0]
            _me = self.picked_cid or 0
            if not _me or _c == _me:
                self.hp = struct.unpack_from('<H', pl, 38)[0]
                self.mp = struct.unpack_from('<H', pl, 42)[0]
                self.hp_max = struct.unpack_from('<H', pl, 50)[0]
                self.mp_max = struct.unpack_from('<H', pl, 54)[0]
                self.hp_t = time.time()
                self.log('   [属性] 0x624 血 %d/%d  蓝 %d/%d'
                         % (self.hp, self.hp_max, self.mp, self.mp_max))
                self.ev.put(('self_hp', {'hp': self.hp, 'max': self.hp_max,
                                         'mp': self.mp, 'mp_max': self.mp_max,
                                         'dead': self.dead}))
                self._auto_heal_check()      # ★ 全量属性到手 → 评一次凝神术
        elif cmd == 0x623 and len(pl) >= 12:
            # s_nSC_CharacterAttrUpdate: [u32 实体][u32 属性ID][u32 属性值] × N
            # ★ 实测（真录制 5647 帧，全部正好 12 字节 = 单条）：
            #     3001 = 当前血量   2008 = 血量上限
            #     3002 = 当前法力   2009 = 法力上限
            #   其它属性 ID（4010/4011/6001/4000/4001…）是状态标志，不是血量。
            #   ⚠ 以前把「属性ID」当血量，再猜「>2500 就是上限」，所以血量一直是鬼数字。
            me = self.picked_cid or 0
            for i in range(len(pl) // 12):
                e, attr, val = struct.unpack_from('<III', pl, i * 12)
                if me and e == me:
                    self._note_self_attr(attr, val)
                    continue
                if not (EID_NPC_LO <= e <= EID_NPC_HI):
                    continue                      # 只跟 NPC 段（玩家跳过）
                if attr not in (3001, 2008):
                    continue
                o = self._ent(e)
                o['t'] = time.time()
                if attr == 2008:
                    o['hpmax'] = val
                    continue
                if val == 0 and o['hp'] and o['name'] and not o.get('dead_seen'):
                    o['dead_seen'] = True
                    o['dead_t'] = time.time()
                    self.bot_kills += 1
                    self.log('   [打怪] %s 已倒下（本次累计 %d）'
                             % (o['name'], self.bot_kills))
                o['hp'] = val
        elif cmd == 0x646:
            # ★ s_nSC_PlayerRelived —— 服务端确认复活
            #   活过来之后位置会被搬到复活点，旧坐标作废，距离必须重算
            self.dead = False
            self.hp = self.hp_max
            self._relive_pending = False
            self.relive_try = 0
            self._pos_unconfirmed = time.time()
            self.log('   ★★ 复活成功（0x646）—— 位置已变，'
                     '重新传送一次或等 0x62b 才能算准距离')
            self.ev.put(('relive_res', {'ok': True}))
            self.ev.put(('self_hp', {'hp': self.hp, 'max': self.hp_max,
                                     'dead': False}))
        elif cmd == 0x72E:
            self.log('   服务端 FightBOT 状态 0x72e：%s' % pl.hex())
        elif cmd == 0x625 and len(pl) >= 6:
            # ★★★ s_nSC_InitPlayerSkill —— 角色**已学会的技能清单**
            #   载荷 = [u32 角色ID][u16 数量 N][u32 技能ID × N]
            #   真录制（角色 0x72b=1835）78 字节 = 6 + 18×4，N=17：
            #     eb030000 ea030000 eb030000 ed030000 5a1b0000 ...
            #     → 1003 冲击 / 1002 / 1005 / 7002 伤痛咒 / 7043 / 7062 风寒蛊 / ...
            self._note_learned(pl)
        elif cmd == 0x648 and len(pl) >= 20:
            self._note_skill_ack(pl)
        elif cmd == 0x60A and len(pl) >= 16:
            # ★★★ s_nSC_SkillBroadcast（玩家/怪物施法广播）—— 2026-10-20 抓包定案
            #   [u32 施法者][u32 技能ID][u32 step][u32 目标][...]
            #   实测：真客户端发 0x408(7002) 后 0.03s 服务端就回这条，技能=7002/step=6。
            #   **这才是「技能真的放出去了」的权威信号** —— 比自己发的 0x408 可靠得多。
            _who, _sk, _sp, _tg = struct.unpack('<IIII', pl[:16])
            if _who == (self.picked_cid or 0):
                self.atk_ack += 1
                self.skill_ack_ids.add(_sk)
                VERIFIED.add(_sk)
                # ★★★★ 2026-10-20 修「明明放出来了却记成不能用」：
                #   服务端广播的 _sk 是**实际形态ID**，跟我们发的 ID 不一定相同。
                #   实测：我们发 7062(风寒蛊) → 服务端回 7082(也是风寒蛊)；
                #         我们发 7003(伤痛咒) → 服务端回 7281(噬灵蛊，同门派变身形态)。
                #   所以**必须把刚发出去的那个 ID 也标成已验证**，
                #   否则下拉里 7062 永远没有 ✓，用户以为它放不出来。
                _sent = self._last_cast_sk or 0
                if _sent and _sent != _sk and \
                        time.time() - self._last_cast_t < 3.0:
                    VERIFIED.add(_sent)
                    self.ev.put(('skill_seen', {'id': _sent, 'cd': 0}))
                if _sk in HIDDEN:
                    HIDDEN.discard(_sk)
                    save_state()
                self._last_ack_t = time.time()
                self._ack_skill = _sk
                # 服务端确认 → 记账（前置技能上线 / 清零无响应计数）
                self._note_cast_ok(_sent)
                # ★ 2026-10-20 新增：刚从「使用」按钮发出去的技能回了广播
                #   → 这次是自我施法（BUFF/治疗/姿态），单独计数并给 UI 一个明确回执。
                #   不能算进「攻击命中」，否则上面那行「累计」会虚高。
                #   ⚠ 判断用「我发出去的 ID」而不是「服务端回的 ID」：
                #     服务端会回实际形态（发 7003 回 7281），拿回包 ID 比会永远不等。
                if (self._use_skill == _sent and self._use_t
                        and self._last_ack_t - self._use_t < 3.0):
                    self.use_ack += 1
                    self.ev.put(('use_res', {'ok': True, 'ack': True,
                                             'id': _sk,
                                             'name': (skill_cfg(_sk) or {}).get('name')
                                             or ('技能%d' % _sk)}))
                    self.log('   ★ 自我施法成功 0x60a：%s(%d) step %d（BUFF 生效）'
                             % ((skill_cfg(_sk) or {}).get('name') or '技能',
                                _sk, _sp))
                elif self._cast_log < 6 or self.atk_ack % 20 == 0:
                    self._cast_log += 1
                    self.log('   ★ 施法成功 0x60a：技能 %d step %d → 0x%08x'
                             '（累计 %d）' % (_sk, _sp, _tg, self.atk_ack))
                self.ev.put(('skill_seen', {'id': _sk, 'cd': 0}))
        elif cmd == 0x610 and len(pl) >= 12:
            _t, _f, _c = struct.unpack('<III', pl[:12])
            if _c == (self.picked_cid or 0):
                self.atk_hit += 1
                o = self.ent.get(_t)
                if o:
                    o['t'] = time.time()
                if self.atk_hit <= 3 or self.atk_hit % 20 == 0:
                    self.log('   ✓ 命中广播 0x610：目标 0x%08x（累计命中 %d）'
                             % (_t, self.atk_hit))
        # ========================================================================
        elif cmd == 0x798 and len(pl) >= 4:
            # 心跳应答：原样回显我们发出的 4 字节（ping-reply），仅用于算延迟/判定存活
            self.hb = struct.unpack('<I', pl[:4])[0]
            self.hb_t = time.time()
            self.hb_ack_t = time.time()
        elif cmd == 0x71d and len(pl) >= 4:
            # ★ 服务端时钟广播（权威）：8B = [u32 毫秒时钟][u32 Unix秒]，每 ~12.9 秒一次
            self.srv_hb = struct.unpack('<I', pl[:4])[0]
            self.srv_hb_t = time.time()

    # ================================================================ 站桩自动打怪
    # ---------------- ① 进入场景序列
    def _scene_build(self):
        """构造进入场景序列 —— 真客户端实测时序（载荷取自 脱机进世界.py）

        0x47e 是「我现在要看世界了」的 AOI 握手：
            载荷 = [u32 4+N*4][u32 N][u32 元素 × N]
        真客户端第一发固定两元素 = [1, 自身角色号]；服务端收到才下发实体清单 0x647。
        这一串不发 → 角色永远不算「在 AOI 里」，之后技能 / 自动战斗全被静默丢弃。
        """
        cid = (self.picked_cid or 0) & 0xFFFFFFFF
        mid = (self.map_id or 0) & 0xFFFFFFFF
        wt = (self.wtime or WTIME_FALLBACK) & 0xFFFFFFFF
        ln = ((self.cur_line or {}).get('name') or '').encode('gbk')
        # 0x4fe 的线路名在 [8:32]，整包固定 136 字节
        reg = (b'\x00' * 8 + ln + b'\x00' * 128)[:136]
        aoi = struct.pack('<II', 12, 2) + struct.pack('<II', 1, cid)
        seq = [
            (0.35, 0x47E, aoi),                                     # ← AOI 握手首查，必须最先
            (0.50, 0x515, struct.pack('<I', cid)),
            (0.52, 0x4FE, reg),                                     # 登记进本场景
            (0.53, 0x4FF, b'\x77'),
            (0.54, 0x425, struct.pack('<I', mid) +
             bytes.fromhex('001000004010000000120000c0120000')),
            (0.54, 0x4FD, struct.pack('<I', cid)),
            (0.54, 0x47E, bytes.fromhex('0400000000000000')),
            (0.62, 0x52E, struct.pack('<I', cid) + b'\x01\x00\x00\x00' + b'\x00' * 101),
            (0.62, 0x52E, struct.pack('<I', cid) + b'\x01\x00\x00\x00' + b'\x00' * 101),
            (0.62, 0x41D, struct.pack('<I', cid) + struct.pack('<I', wt) + b'\x17\x00'),
            (0.74, 0x41A, bytes.fromhex('00001a00')),
            # 进场景收尾一批（真客户端一口气发完，之前全漏了）
            (0.80, 0x4B6, struct.pack('<I', cid)),
            (0.80, 0x463, struct.pack('<I', cid) + b'\x00' * 8),
            (0.80, 0x411, bytes.fromhex('7600000000000000')),
            (0.80, 0x4D7, b'\x00'),
            (0.80, 0x431, struct.pack('<I', cid) + b'\x02'),
            (1.00, 0x52E, struct.pack('<I', cid) + b'\x01\x00\x00\x00' + b'\x00' * 101),
            (1.05, 0x41A, bytes.fromhex('00001a00')),                # 真客户端发两次
            (1.08, 0x537, bytes.fromhex(
                '7838d26a650000007838d26a190000007938d26a'
                '000000000000000000000000')),
        ]
        # 连续空查：只发 1 次会让场景加载卡在开头，必须刷够次数
        for i in range(SCENE_SPAM_47E):
            seq.append((0.90 + i * 0.028, 0x47E, struct.pack('<II', 4, 0)))
        # ★ 必须按时间排序：_scene_step 用游标推进，时间非单调会让后段包堆在一起一次性喷出
        seq.sort(key=lambda x: x[0])
        return seq

    def _scene_step(self):
        if self.w is None:
            return
        sc = self.scene
        el = time.time() - sc['t0']
        if sc['seq'] is None:
            if el < 0.34:
                return
            sc['seq'] = self._scene_build()
            self.log('   → 场景序列就绪：角色号=0x%x 地图=%s 世界时间=0x%08x'
                     % ((self.picked_cid or 0), self.map_id,
                        self.wtime or WTIME_FALLBACK))
        while sc['i'] < len(sc['seq']) and el >= sc['seq'][sc['i']][0]:
            c, p = sc['seq'][sc['i']][1], sc['seq'][sc['i']][2]
            try:
                self.w.sendall(wframe(c, p))
            except Exception as ex:
                self.log('[!] 场景包 0x%03x 发送失败：%s' % (c, ex))
                return
            sc['i'] += 1
        if sc['i'] >= len(sc['seq']):
            sc['done'] = True
            n = len(self.ent)
            self.log('   ★ 进入场景序列已全部发出（角色应已激活）')
            self.log('     已登记实体 %d 个；可以点「站桩打怪」了' % n)

    # ---------------- ② 实体台账
    def _ent(self, eid):
        o = self.ent.get(eid)
        if o is None:
            o = self.ent[eid] = {'x': None, 'y': None, 'z': None, 't': 0.0,
                                 'rawx': None, 'rawy': None,
                                 'name': '', 'hp': None, 'hpmax': None,
                                 'mnid': 0, 'lvl': '', 'title': '', 'kind': None}
        return o

    def _xy_of(self, o):
        """取实体的世界坐标。

        优先用 0x647 / 0x6D3 / 0x6D4 给的绝对浮点坐标（精确、实时）；
        没有就用 0x6B9 里那个 16 位定点坐标，拿自己位置反推圈数解出来。
        后者是「刷新点」位置，站桩不动的怪全靠它 —— 以前这里空着，
        整张怪物表都是「距离?」，所以既没有距离也没有排序。
        """
        if o['x'] is not None:
            return o['x'], o['y']
        ux, uy = o.get('rawx'), o.get('rawy')
        if ux is None or not self.pos or not (ux or uy):
            return None, None
        x = fix16(ux, self.pos[0], COORD_MOD_X)
        y = fix16(uy, self.pos[1], COORD_MOD_Y)
        if not (0 < x < 20000 and 0 < y < 20000):
            return None, None
        return x, y

    def _setpos(self, eid, ux, uy, uz):
        """0x6D3 / 0x6D4 的 u16 坐标换算成世界坐标"""
        x, y, z = ux / COORD_SCALE, uy / COORD_SCALE, uz / COORD_SCALE
        if not (0 < x < 20000 and 0 < y < 20000):
            return
        me = self.picked_cid or 0
        if me and eid == me:
            self.pos = (x, y, z)
            return
        # ★ 0x6D3/0x6D4 是「所有会动的东西」的广播，里面有玩家、召唤兽、场景物件。
        #   这些根本没有 0x647/0x6B9 身份，登记进来只会变成一串没名字的「未知」。
        #   只收 NPC 段（0x0260xxxx~0x0280xxxx）。
        if not (EID_NPC_LO <= eid <= EID_NPC_HI):
            return
        o = self._ent(eid)
        o['x'], o['y'], o['z'] = x, y, z
        o['t'] = time.time()
        # ★ 只有坐标、没有身份的 → 主动问一次（0x46e Req 4B）。
        #   有些实体只从坐标包出现（新刷出来的怪就是这样），没有 0x6B9 身份包，
        #   不问就永远显示「未知」，而且**分不清是怪还是别人的宠物**，
        #   选目标时只能瞎猜 —— 这就是「附近有怪不打」的根子。
        #   ⚠ 光发 0x46E 服务端不一定理；进 World 时能拿到名字靠的是
        #     0x47E 批量查（`_query_pending`），所以这里也塞进 ent_pend。
        if not (o.get('mnid') or o.get('name')) and eid not in self.rp_req:
            self.rp_req.add(eid)
            if self.w is not None:
                try:
                    self.w.sendall(wframe(0x46E, struct.pack('<I', eid)))
                except Exception:
                    pass
            if eid not in self.ent_queried:
                self.ent_pend.append(eid)

    def _fill_ident(self, eid, mnid):
        """用 MNID 填实体的名字/等级/称号/类型"""
        o = self._ent(eid)
        self._revive_if_respawn(eid, o)     # 刷新点复用ID：清掉上一只的死亡状态
        o['mnid'] = mnid
        o['t'] = time.time()
        inf = mnid_info(mnid)
        if inf:
            o['name'] = inf[0]
            o['lvl'] = inf[1]
            o['title'] = inf[2]
            o['kind'] = inf[3]
            return inf
        # MNID 表里没有：留个记号，方便以后补表
        if self._unk_mnid < 12:
            self._unk_mnid += 1
            self.log('   [身份] MNID %d 不在表里（eid 0x%08x）' % (mnid, eid))
        return None

    def _ent_kind(self, o):
        """优先用 MNID 判出的类型，退回名字查表"""
        k = o.get('kind')
        if k:
            return k
        return npc_kind(o.get('name') or '')

    def _parse_647(self, pl):
        """0x647 s_nSC_RspNpcInScene —— 实体清单，纯脱机拿「怪名 + 坐标」的唯一来源

        头 8 字节 = [u16 类型=1][u16 数量 N][u32 保留]
        之后 N 条 × 39 字节（0x27）：
            +0x00 f32 x ｜ +0x04 f32 y ｜ +0x08 f32 z
            +0x0C u32 实体ID（段 0x02620000~0x027FFFFF）
            +0x10 u8 × 3 标志
            +0x13 GBK 名字（最多 20 字节，0 结尾）
        """
        if len(pl) < 8:
            return 0
        cnt = struct.unpack('<H', pl[2:4])[0]
        off, n = 8, 0
        for _ in range(cnt):
            if off + 39 > len(pl):
                break
            try:
                x, y, z = struct.unpack('<fff', pl[off:off + 12])
                eid = struct.unpack('<I', pl[off + 12:off + 16])[0]
                nm = pl[off + 0x13:off + 39].split(b'\x00')[0] \
                    .decode('gbk', 'ignore').strip()
            except Exception:
                off += 39
                continue
            if 0 < x < 20000 and 0 < y < 20000 and EID_NPC_LO <= eid <= EID_NPC_HI:
                o = self._ent(eid)
                o['x'], o['y'], o['z'] = x, y, z
                o['t'] = time.time()
                if nm:
                    o['name'] = nm
                self._revive_if_respawn(eid, o)
                n += 1
            off += 39
        return n

    def _revive_if_respawn(self, eid, o):
        """★ 修「怪刷新出来了却永远不打」（2026-10-20）

        有些刷新点**复用同一个实体ID**：上一只倒下时 0x623 把 hp 记成 0，
        新的一只刷出来时服务端不再发血量（客户端默认满血），于是这条记录的
        hp 永远是 0 → `_npc_list` 当死人剔掉 → 列表里有它、打怪却绕过它。
        这里看到它**重新出现**（0x647 清单 / 0x6B9 身份）就把死亡状态清掉。
        ⚠ 加 3 秒门槛：刚死那会儿服务端还会重复推几次同一个实体，别误复活。
        """
        if not o.get('dead_seen'):
            return
        if time.time() - (o.get('dead_t') or 0.0) < 3.0:
            return
        o['dead_seen'] = False
        o['hp'] = None
        o['hpmax'] = None
        self.log('   [刷新] %s 又刷出来了（0x%08x）—— 重新纳入目标'
                 % (o.get('name') or '怪', eid))

    def _npc_list(self, max_age=None, radius=None, with_bl=False):
        """范围内的实体，按距玩家由近到远。**已剔除纯 NPC**

        返回 [(距离, 名字, 实体ID, 血量, 血上限, 类型, 等级)]

        with_bl=False（默认）→ 界面上打了 ✗ 的怪**不进列表**，所有打怪路径
                              拿到的都是「可以打」的；
        with_bl=True          → 排除了的怪也列出来（只给界面显示用，好让人
                              再点一下取消排除），**别拿它去挑目标**。

        ⚠ 别拿时间做"活着"的判据：0x62B 只推「在动」的实体，
          站着不动的怪和 NPC 从 0x647 之后再也不会有坐标更新。
          原来用 30 秒 TTL，结果进场景 30 秒后整张台账全被判过期 → 列表永远空。
          这里默认给 10 分钟，过期只用来兜底清理换地图后的残留。
        """
        if not self.pos:
            return []
        r = self.radius if radius is None else radius
        ttl = ENT_TTL if max_age is None else max_age
        mx, my = self.pos[0], self.pos[1]
        now, out = time.time(), []
        self._diag = {'all': 0, 'npc': 0, 'dead': 0, 'far': 0, 'noxy': 0,
                      'blk': 0, 'skip': 0}
        for eid, o in self.ent.items():
            self._diag['all'] += 1
            if now - o['t'] > ttl:
                continue
            if o['hp'] is not None and o['hp'] <= 0:
                self._diag['dead'] += 1
                continue
            # ★ 坐标：优先 0x647/0x6D3/0x6D4 的绝对坐标，其次 0x6B9 的定点坐标
            #   （用自己位置反推圈数）。以前后者没接，整张表都是「距离?」，
            #   于是既看不到距离，也没有任何排序可言。
            ex, ey = self._xy_of(o)
            d = -1.0
            if ex is not None:
                d = ((ex - mx) ** 2 + (ey - my) ** 2) ** 0.5
                if d > r:
                    self._diag['far'] += 1
                    continue
            else:
                self._diag['noxy'] += 1
            nm = o['name'] or ''
            k = self._ent_kind(o)
            # ★ 排除名单：界面上打了叉的怪，刷新出来（新实体ID、同名）也不打
            #   没名字的实体只能按实体ID排除（名字都是「未知」，按名字会把
            #   所有未解析实体一起排除掉）
            _key = nm or ('0x%08x' % eid)
            if _key in self.bl and not with_bl:
                self._diag['blk'] += 1
                continue
            if k == 'NPC' and not self.show_npc:
                self._diag['npc'] += 1
                continue
            # ★ 连打几次服务端都不理的怪：先跳开一会儿，别一直卡在它身上
            if now < self._skip_t.get(eid, 0.0):
                self._diag['skip'] += 1
                continue
            out.append((d, nm or '未知', eid, o['hp'], o['hpmax'],
                        k, o.get('lvl') or ''))
        # 有坐标的按距离排前面，没坐标的排后面
        out.sort(key=lambda t: (1 if t[0] < 0 else 0,
                                t[0] if t[0] >= 0 else 0.0))
        return out

    def _empty_hint(self):
        """列表为空时给一句人话，说明是哪一层过滤掉的"""
        if not self.pos:
            return '还没有自己的坐标（0x603 / 0x62B 没到）'
        d = self._diag or {}
        if not d.get('all'):
            return '实体台账是空的（0x647 没收到，或刚传送过还没重新拉取）'
        parts = ['台账 %d 个' % d.get('all', 0)]
        if d.get('npc'):
            parts.append('NPC %d 个已剔除' % d['npc'])
        if d.get('dead'):
            parts.append('已死 %d 个' % d['dead'])
        if d.get('blk'):
            parts.append('已排除 %d 个（打叉的不打）' % d['blk'])
        if d.get('skip'):
            parts.append('打不动先跳过 %d 个' % d['skip'])
        if d.get('far'):
            parts.append('超出 %d 米 %d 个' % (int(self.radius), d['far']))
        if d.get('noxy'):
            parts.append('无坐标 %d 个（已按在视野内算入）' % d['noxy'])
        return '附近没怪（%s）' % '，'.join(parts)

    # ---------------- ④0 使用技能（BUFF / 治疗类，不需要目标）
    def do_use_skill(self, skill=0, group=0, step=0, eid=0):
        """就放一次技能，**不挑怪、不查距离、不查射程**

        给 BUFF / 治疗 / 姿态 / 回城 这类用：它们不作用在别人身上，
        服务端只需要知道「谁在放什么」。
        `0x408` 的 [6] 目标字段填**自己** —— 这是脱机端的通行做法：
        服务端按「施法者==目标」就理解成自我施法，不会去 AOI 里找目标。
        攻击类技能也能用（目标填自己时服务端多半不理），想打怪用技能格的
        「开始」自动打，或先把怪选中再点通用格/攻击格手动放。
        """
        if not self.in_world or self.w is None:
            self.log('[!] 使用技能失败：当前不在世界中')
            self.ev.put(('use_res', {'ok': False, 'msg': '未进入世界'}))
            return False
        if not self.scene['done']:
            self.log('[!] 使用技能失败：场景序列还没跑完')
            self.ev.put(('use_res', {'ok': False, 'msg': '场景未就绪'}))
            return False
        cid = (self.picked_cid or 0) & 0xFFFFFFFF
        if not cid:
            self.log('[!] 使用技能失败：拿不到角色ID')
            self.ev.put(('use_res', {'ok': False, 'msg': '无角色ID'}))
            return False
        if not skill:
            skill = self._pick_default_skill()
        # ★ 组值/step 按「目标是不是自己」取（2026-10-20 真包 41 帧定案）：
        #   自我施法 = 391/5 + 目标填自己；攻击 = 392/6 + 目标填怪。
        #   ⚠ 以前这里恒取 392/6，自我施法类技能（调元/凝神术/惊天动地/
        #      血祭/野兽之魂）因此全被服务端静默丢弃 —— 根因就在这两行。
        _self, _stp, _grp = cast_profile(skill)
        if not group:
            group = _grp
        if not step:
            step = _stp
        cfg = skill_cfg(skill) or {}
        # ⚠ 2026-10-20 **推翻**了我自己半小时前的判断：
        #   我一度以为 `HavetoEquip=1`（需装备武器/法宝）是 7xxx 全灭的根因，
        #   并在这里直接 return False 拦掉。**那是错的，已撤回。**
        #   证据：这次录制里角色 0x72b 用 7002 伤痛咒（HavetoEquip=1）
        #   连放 5 次，服务端每次都回 0x60A 确认施法成功。
        #   → HavetoEquip 只影响「客户端界面上技能是否亮」，不影响服务端受理。
        #   所以这里只提示一句，照常发包。
        # ★★★ 2026-10-20 关键修正：按 SkillTarget 决定目标是谁
        #
        #   以前这里一律 `tgt = cid`（填自己），结果所有
        #   `SkillTarget=1` 的攻击技能（1002/1003/7101/7062…）全部放不出去 ——
        #   服务端拿到「打自己」根本不知道要打谁，直接丢弃。
        #   用户实测就是这么翻车的：17 个技能只有 3 个「成功」。
        #
        #   现在的规则：
        #     nosel=True  (SkillTarget=0) → 目标填自己，原地放
        #     nosel=False (SkillTarget=1) → 必须挑一只活怪，先 0x43D 锁目标
        tgt = eid & 0xFFFFFFFF if eid else 0
        # ★ 自我施法类（SELFCAST）：[6] 永远填自己、step=5、组=391，
        #   且不发 0x43D。真客户端录制 20261020_180502 实证：
        #   1005/7043/7161/7461/7321 全部「自己 + step5 + 组391」。
        #   以前把它们当攻击技能发给最近的怪 + step=6 → 服务端静默丢弃。
        need_tgt = (not eid and not cfg.get('nosel')) and not _self
        if _self:
            tgt = cid
        elif need_tgt:
            _t, _tn, _td = self._nearest_target()
            if not _t:
                self.log('[!] %s 需要目标，但附近没怪 —— 站到怪旁边再点'
                         % (cfg.get('name') or ('技能%d' % skill)))
                self.ev.put(('use_res', {'ok': False, 'msg': '这个技能要目标，附近没怪'}))
                return False
            rng = cfg.get('rng') or 0
            if rng and _td * 100.0 > rng:
                self.log('[!] %s 射程 %gm，最近的 %s 在 %.1fm —— 走近点'
                         % (cfg.get('name') or '', rng / 100.0, _tn, _td))
                self.ev.put(('use_res', {'ok': False,
                                         'msg': '超出射程 %.1fm' % _td}))
                return False
            tgt = _t & 0xFFFFFFFF
        elif not tgt:
            # 不需要目标的技能：[6] 填谁？
            #   以前一律填自己。但真录制里 7002 伤痛咒（SkillTarget=0）**13 帧
            #   全填的是怪物实体ID**（0x02625c80 那一段），一次都没填过自己。
            #   说明 [6] 是「当前选中的东西」，不是「施法作用对象」。
            #   所以：附近有怪就填怪（更贴近真客户端），没怪才填自己兜底
            #   （1005/20006 用「自己」实测能被受理，兜底安全）。
            _t, _tn, _td = self._nearest_target()
            tgt = (_t & 0xFFFFFFFF) if _t else cid
        # 冷却/蓝/血/前置 统一在这里拦，拦下次都把原因说清楚（带数字）
        now = time.time()
        _blk = self._cast_block(skill)
        if _blk:
            self.log('[!] %s' % _blk)
            self.ev.put(('use_res', {'ok': False, 'msg': _blk}))
            return False
        # ★ 防连发：同一个技能 400ms 内重复点 = 双击/手抖，只发一次
        #   （用户实测时一次点击发了 8 条，全是白发的无效包，还会把服务端
        #     的施法状态搅乱，导致后面连本来能放的技能也放不出）
        if (self._use_skill == skill and self._use_t
                and now - self._use_t < 0.4):
            self.ev.put(('use_res', {'ok': False, 'msg': '刚按过，稍等'}))
            return False
        # 需要目标的技能：先 0x43D 锁目标（真客户端是两步）
        if need_tgt:
            try:
                self.w.sendall(wframe(0x43D, struct.pack('<II', cid, tgt)))
            except Exception:
                pass
        # 给自己用（BUFF类）就不发 0x43D，免得把「打怪目标」取消掉
        body = struct.pack('<9I', cid, skill & 0xFFFFFFFF, 0, 0,
                           group & 0xFFFFFFFF, step & 0xFFFFFFFF, tgt,
                           ATTACK_ARG7 & 0xFFFFFFFF, ATTACK_TAIL & 0xFFFFFFFF)
        try:
            self.w.sendall(wframe(0x408, body))
        except Exception as ex:
            self.log('[!] 使用技能发送失败：%s' % ex)
            self.ev.put(('use_res', {'ok': False, 'msg': str(ex)}))
            return False
        cfg = skill_cfg(skill) or {}
        nm = cfg.get('name') or ('技能%d' % skill)
        self.use_sent += 1
        self._use_t = now
        self._use_skill = skill
        self._ack_watch = True            # 等 1.5 秒看服务端理不理（_tick 里查）
        self.log('   [使用] %s(%d) 组 %d step %d → 目标 0x%08x（自我施法）'
                 % (nm, skill, group, step, tgt))
        self.ev.put(('use_res', {'ok': True, 'id': skill, 'name': nm}))
        return True

    # ---------------- ④ 攻击（0x408 s_nCS_CharacterUseSkill）
    def do_attack(self, eid=0, skill=0, group=0, step=0, auto=False):
        """对指定怪物放一次技能。eid=0 时自动挑最近的活怪。"""
        if not self.in_world or self.w is None:
            self.log('[!] 攻击失败：当前不在世界中')
            self.ev.put(('atk_res', {'ok': False, 'msg': '未进入世界'}))
            return False
        if not self.scene['done']:
            self.log('[!] 攻击失败：场景序列还没跑完（角色未激活）')
            self.ev.put(('atk_res', {'ok': False, 'msg': '场景未就绪'}))
            return False
        cid = (self.picked_cid or 0) & 0xFFFFFFFF
        if not cid:
            self.log('[!] 攻击失败：拿不到角色ID')
            self.ev.put(('atk_res', {'ok': False, 'msg': '无角色ID'}))
            return False
        if not skill:
            skill = self._pick_default_skill()
        # ★ group/step 按「目标是不是自己」取（2026-10-20 真包 41 帧定案）：
        #   自我施法 = 391/5 + 目标填自己；攻击 = 392/6 + 目标填怪。
        #   ⚠ 以前这里恒取 392/6（注释还写着「全场常量」）—— 那只对攻击成立，
        #      自我施法类因此全被服务端静默丢弃，根因就在这两行。
        cfg = skill_cfg(skill)
        _self, _stp, _grp = cast_profile(skill)
        if not group:
            group = _grp
        if not step:
            step = _stp
        # ⚠ HavetoEquip=1 并不阻止施法（录制实证：7002 需装备却成功 5 次），不拦
        # ★ 自我施法类不走攻击路径：目标是自己、step=5、组=391，
        #   直接转给「使用」（2026-10-20 修「血祭/野兽之魂放不出来」——
        #   这两个在配置表里没有行，被误判成攻击技能发给怪，服务端丢弃）
        # ⚠ 2026-10-21 试过把 `or cfg.get('nosel')` 删掉、改成只认 _self，
        #   **当场撤回**：真客户端对 7002/7361 这类 SkillTarget=0 的技能
        #   本来就不发 0x43D（_selftest_selfcast 第 [3] 组就是拿真包立的规矩），
        #   去掉它反而是偏离真包。这个 nosel 分支必须留着。
        if _self or (cfg and cfg.get('nosel')):
            return self.do_use_skill(skill=skill, group=group, step=step)
        rng_m = (cfg['rng'] / 100.0) if (cfg and cfg['rng']) else DEFAULT_RANGE_M
        rng_src = '' if (cfg and cfg['rng']) else '（配置表没写，按默认）'
        # 显式给了射程就用界面的（用户可自己填）
        if getattr(self, 'range_m', 0):
            rng_m = self.range_m
            rng_src = '（界面指定）'
        # 目标：没指定就自动挑最近的
        if not eid:
            ns = self._npc_list()
            if not ns:
                if auto:
                    # 自动模式每 5 秒最多念一次，别刷屏
                    if time.time() - getattr(self, '_hint_t', 0) > 5.0:
                        self._hint_t = time.time()
                        self.log('   [自动] %s' % self._empty_hint())
                else:
                    hint = self._empty_hint()
                    self.log('[!] 攻击失败：%s' % hint)
                    self.ev.put(('atk_res', {'ok': False, 'msg': hint}))
                return False
            eid = ns[0][2]
            # 自动模式只在射程内出手，免得对着 40 米外的怪空放
            if auto and rng_m > 0:
                near = [t for t in ns if t[0] >= 0 and t[0] <= rng_m]
                if not near:
                    if time.time() - getattr(self, '_hint_t', 0) > 5.0:
                        self._hint_t = time.time()
                        d0, nm0 = ns[0][0], ns[0][1]
                        self.log('   [自动] 最近的 %s 在 %.1f m，超出技能 %d 的 '
                                 '%.1f m 射程 —— 走近点' % (nm0, d0, skill, rng_m))
                    return False
                eid = near[0][2]
        # 冷却/蓝/血/前置 统一拦截，原因带数字（自动模式只默默跳过，不刷屏）
        now = time.time()
        _blk = self._cast_block(skill)
        if _blk:
            if not auto:
                self.log('[!] %s' % _blk)
                self.ev.put(('atk_res', {'ok': False, 'msg': _blk}))
            return False
        if now - self.last_atk_t < ATTACK_MIN_GAP:
            return False
        self.last_atk_t = now
        body = struct.pack('<9I', cid, skill & 0xFFFFFFFF, 0, 0,
                           group & 0xFFFFFFFF, step & 0xFFFFFFFF,
                           eid & 0xFFFFFFFF, ATTACK_ARG7 & 0xFFFFFFFF,
                           ATTACK_TAIL & 0xFFFFFFFF)
        assert len(body) == 36
        try:
            # ★★ 先发 0x43D 锁定目标，再发 0x408 放技能。
            #   真录制里攻击前紧贴着一条 0x43D（8 字节 = [角色ID][目标ID]），
            #   目标ID 与随后 0x408 的 [6] 完全一致 —— 不先锁定，服务端不知道该打谁。
            # 0x43D = s_nCS_SetSelectTarget（选中目标）。
            # 真客户端是「选中一次、连打多次」，所以只在换目标时才发，
            # 免得每次都重新选中把服务端的状态搅乱。
            #
            # ⚠ 2026-10-20 查证：0x405 是 s_nCS_PlayerDirection（**人物朝向**），
            #   载荷 [u32 朝向/位置][u32 自己]，跟攻击目标毫无关系
            #   （录制里 0x405 的 [0] 全在 0x4000xxxx 段，而 0x408 的目标在 0x026xxxxx 段）。
            #   我一度以为它是「目标确认包」并加进来，那是错的 —— 已撤掉，别再加。
            if eid != self.atk_target:
                self.w.sendall(wframe(0x43D, struct.pack('<II', cid,
                                                         eid & 0xFFFFFFFF)))
            self.w.sendall(wframe(0x408, body))
            self.atk_sent += 1
            # ★★★★ 2026-10-20：记下「我这一发到底发的哪个技能」。
            #   服务端 0x60A 回的是**实际形态ID**（发 7062 → 回 7082、发 7003 → 回 7281），
            #   不能拿回包的 ID 反推我发的技能能不能用。见 0x60A 处理里那段注释。
            self._ack_skill = int(skill)
            self._last_cast_sk = int(skill)
            self._last_cast_t = time.time()
            # ★ 攻击也挂「回响看守」（原来只有通用技能挂）：
            #   1.5 秒内服务端既没 0x648 也没 0x60A → 记一次失败，
            #   同一只怪连着 3 次没人理就冷藏 30 秒换目标（_cast_note_fail 里）。
            #   没有这一条，锁在一只「打不动的怪」上会一直打下去。
            self._ack_watch = True
            self.atk_target = eid
            o = self.ent.get(eid)
            nm = (o or {}).get('name') or ('0x%08x' % eid)
            d = -1.0
            if self.pos and o and o['x'] is not None:
                d = ((o['x'] - self.pos[0]) ** 2 +
                     (o['y'] - self.pos[1]) ** 2) ** 0.5
            # 自动打怪一秒一发，日志只留前 3 次和每 10 次，免得刷屏
            if not auto or self.atk_sent <= 3 or self.atk_sent % 10 == 0:
                self.log('   [攻击] #%d → %s 0x%08x（%s / 射程 %.0fm%s）'
                         '技能 %d 组 %d step %d'
                         % (self.atk_sent, nm, eid,
                            ('%.1f m' % d) if d >= 0 else '距离?',
                            rng_m, rng_src, skill, group, step))
            if not auto:
                self.ev.put(('atk_res', {'ok': True, 'eid': eid, 'name': nm,
                                         'n': self.atk_sent}))
            return True
        except Exception as ex:
            self.log('[!] 攻击发送失败：%s' % ex)
            self.ev.put(('atk_res', {'ok': False, 'msg': str(ex)}))
            return False

    def set_auto_atk(self, on, skill=None, group=0, step=0, combo=None):
        """自动打怪：每 tick 挑最近的活怪放技能

        combo: 技能组合（连招）序列 [(技能ID, 组, step), ...]，按顺序循环放。
               为空就只放单个技能。

        ★★★ 2026-10-20 修「界面开启后组/step 是 0」：
           日志里出现过 `[自动] 已开启 —— 技能 7002（组 0 / step 0）`，
           然后 0x408 就带着 [4]=0 [5]=0 发出去 —— 服务端只看这一条就丢弃了，
           连 0x648 都不回。界面调用时只传了 skill，group/step 吃到了这里的
           默认值 0。现在：**传 0 就当作「没指定」，一律回落到配置/常量**。
        """
        # ★ 组值/step 兜底：0 = 让下面按技能自身档案补齐
        #   （自我施法 = 391/5，攻击 = 392/6，见 cast_profile）
        if skill:
            _self, _stp, _grp = cast_profile(skill)
            g = int(group or 0) or _grp
            st = int(step or 0) or _stp
            skill = int(skill)
        else:
            g, st = int(group or 0), int(step or 0) or DEFAULT_STEP
        self.combo = []
        for _x in (combo or []):
            _sid = int(_x[0])
            _sc, _stp2, _grp2 = cast_profile(_sid)
            _g = int(_x[1]) if len(_x) > 1 and _x[1] else _grp2
            _s = int(_x[2]) if len(_x) > 2 and _x[2] else _stp2
            self.combo.append((_sid, _g, _s))
        self.combo_i = 0
        self.combo_t = 0.0
        self.auto_atk = bool(on) and (bool(skill) or bool(self.combo))
        self.auto_atk_skill = (skill, g, st) if skill else None
        if self.auto_atk:
            if self.combo:
                self.log('   [自动] 已开启 —— 技能组合 %d 招：%s，挑最近的怪'
                         % (len(self.combo),
                            ' → '.join('%d(组%d/步%d)' % (x[0], x[1], x[2])
                                       for x in self.combo)))
            else:
                self.log('   [自动] 已开启 —— 技能 %d（组 %d / step %d），挑最近的怪'
                         % (skill, g, st))
                if not g:
                    self.log('   [!] 技能 %d 组值补不出来（配置表里没这个ID）—— '
                             '服务端会丢弃，换一个已学会的技能' % skill)
        else:
            self.log('   [自动] 已关闭')
        self.ev.put(('auto_res', {'on': self.auto_atk}))

    # ---------------- ⑥b 自动同意组队（2026-10-21 新增）
    def set_auto_team(self, on):
        """别人邀请入队 / 申请入队 / 请求合并时自动回「同意」

        协议依据见 handle_frame 里 0x684/0x685/0x686 那段注释（两场录制实证）。
        这里只切开关，实际应答在收包线程里做 —— 因为那条线程才知道
        当前 socket，也才不会和心跳/打怪抢时序。
        """
        self.auto_team = bool(on)
        self._team_auto_n = 0
        if self.auto_team:
            self.log('   [组队] 已开启 —— 收到组队邀请/入队申请将自动同意')
        else:
            self.log('   [组队] 已关闭 —— 邀请只记日志，不自动应答')
        self.ev.put(('team_res', {'on': self.auto_team}))

    # ---------------- ⑥c 低血蓝自动凝神术（2026-10-21 新增）
    #   用户要求：血**或**蓝低于某个百分比就自动放凝神术，百分比玩家自选。
    #   数据源用 0x624（全量血蓝）+ 0x623（3001/3002 变化量），
    #   判断点放在 _note_self_attr / 0x624 之后 —— 属性一变就评一次。
    HEAL_SKILL_IDS = (10005, 1005, 20019)   # 用户口报 10005，表里 1005，旧ID 20019
    HEAL_MIN_GAP = 2.0                      # 两次自动施法的最小间隔（秒）
    HEAL_HOLD = 6.0                         # 放完观察多久：这期间血蓝在涨就不再放
    HEAL_TICK = 0.3                         # 周期检查间隔（秒）

    def heal_skill_id(self):
        """这次该发哪个 ID 的凝神术

        优先用**本角色真的学到了**那个（0x625 下发的已学清单最权威），
        其次退到客户端技能表里认得的那一个。三个 ID 都是同一个技能的不同编号，
        服务端只认自己表里的那个，所以顺序不能反。
        """
        if self._heal_sid:
            return self._heal_sid
        got = set(self.learned or ())
        for s in self.HEAL_SKILL_IDS:
            if s in got:
                self._heal_sid = s
                return s
        for s in self.HEAL_SKILL_IDS:
            if s in SKILL_DB:
                self._heal_sid = s
                return s
        return self.HEAL_SKILL_IDS[-1]

    def _auto_heal_check(self):
        """血/蓝低于阈值 → 放一次凝神术（带节流 + 技能冷却保护）"""
        if not (self.auto_heal and self.in_world and not self.dead):
            return
        hp, hm = self.hp, self.hp_max
        mp, mm = self.mp, self.mp_max
        if not hm or not mm or hp is None or mp is None:
            return                              # 上限还没到（0x624 没收到），先不判断
        pct = max(1, min(99, int(self.auto_heal_pct or 30))) / 100.0
        low_hp = hp <= hm * pct
        low_mp = mp <= mm * pct
        if not (low_hp or low_mp):
            return
        now = time.time()
        if now - self._heal_t < self.HEAL_MIN_GAP:
            return
        # ★★★ 2026-10-21：凝神术多半是「持续回血/回蓝」，放完就重置。
        #   如果这 6 秒里血蓝确实在往上走，说明它已经生效了 —— 这时候再放
        #   等于反复从头开始，反而看不到回复效果（用户会觉得「放了没用」）。
        #   所以：只要有任意一项在涨，就先让它回，别打断。
        if (self._heal_hp0 is not None
                and now - self._heal_t < self.HEAL_HOLD
                and ((hp > self._heal_hp0) or (mp > self._heal_mp0))):
            return
        sid = self.heal_skill_id()
        if self.skill_cd.get(sid, 0.0) > now:
            return                              # 技能还在冷却，等下一帧
        # ★ 2026-10-21：公共冷却也提前判掉 —— 打怪时所有技能共享 1.5 秒，
        #   不判的话会 post 一条注定被 do_use_skill 拒掉的命令，
        #   还把节流时间占掉，等于白白错过一次机会（日志里就是这么空转的）
        if self.grp_cd > now:
            return
        if not self.scene.get('done'):
            return
        self._heal_t = now
        self._heal_hp0, self._heal_mp0 = hp, mp
        self._heal_n += 1
        _why = ('血' if low_hp else '') + ('蓝' if low_mp else '')
        self.log('   [自动] %s低于 %d%%（血 %d/%d  蓝 %d/%d）→ 放凝神术(%d)'
                 % (_why, int(self.auto_heal_pct), hp, hm, mp, mm, sid))
        # 走命令队列，不在这里直接发包 —— 保持「收包线程只收包」的时序
        self.post('use', skill=sid)

    def _heal_tick(self):
        """周期检查（主循环每轮都调，内部限速 HEAL_TICK 秒）

        ★★★ 2026-10-21 用户反馈「勾了不灵敏、血蓝已经很少了也不用」：
          原来只在 0x623/0x624 属性**变化**时检查，可站着不动、
          或者「射程内没有怪」不打怪的时候根本没有属性包进来 ——
          于是长时间不检查，看起来就像功能没生效。
          主循环本来就是 20Hz 的（cmds.get timeout=0.05），加这一拍最省事。
        """
        now = time.time()
        if now - self._heal_tick_t < self.HEAL_TICK:
            return
        self._heal_tick_t = now
        self._auto_heal_check()

    def set_auto_heal(self, on, pct=None):
        """低血蓝自动凝神术开关 + 阈值（pct 为空则沿用上次）"""
        if pct is not None:
            try:
                self.auto_heal_pct = max(1, min(99, int(float(pct))))
            except (TypeError, ValueError):
                pass
        self.auto_heal = bool(on)
        self._heal_t = 0.0
        self._heal_n = 0
        if self.auto_heal:
            self.log('   [自动] 已开启 —— 血或蓝低于 %d%% 时自动放凝神术(%d)'
                     % (self.auto_heal_pct, self.heal_skill_id()))
        else:
            self.log('   [自动] 低血蓝自动凝神术已关闭')
        self.ev.put(('heal_res', {'on': self.auto_heal,
                                  'pct': self.auto_heal_pct}))

    # ---------------- 使用背包物品（2026-10-21 录制实证）
    def use_item(self, slot, iid, cont=1):
        """使用一件背包物品 —— 0x411 s_nCS_PlayerItemOperation，子操作码 0x07

        ★★★ 2026-10-21 录制实证（场次 20261021_200949，world_41002 block 98）：

            07 01 | 1e00 | 05000000 | cf100000 | a0ded94a | f0340000 | ec570000
             |  |     |        |         |          |          |
             |  |     |        |         |          |          └ 物品ID 22508
             |  |     |        |         |          └ 8 字节「使用上下文」
             |  |     |        |         └ 同上
             |  |     |        └ 自己的 cid = 4303（0x603 里同一个值）
             |  |     └ 固定 5（0x60A 技能包里同位置也是 5）
             |  └ 槽位（u16）
             └ 子操作码 0x07 = 使用物品

          旁边紧跟着服务端回了 0x60A（CharacterUseSkill）和 0x613（背包槽位更新），
          其中 0x60A 的 [16:24] 正好是 a0ded94a f0340000 —— 说明这 8 字节是
          「随物品技能一起下发的目标/上下文」，脱机时没有目标，填 0 即可。
        """
        if self.w is None:
            self.log('[!] 不在世界中，没法使用物品')
            return False
        try:
            _cid = int(self.picked_cid or 0)
            pl = (b'\x07\x01'
                  + struct.pack('<H', int(slot) & 0xFFFF)
                  + struct.pack('<I', 5)
                  + struct.pack('<I', _cid)
                  + b'\x00' * 8
                  + struct.pack('<I', int(iid) & 0xFFFFFFFF))
            self.w.sendall(wframe(0x411, pl))
            self.log('   [物品] 使用 槽位%d 物品%d（0x411 %dB）：%s'
                     % (slot, iid, len(pl), pl.hex()))
            # ★★★ 2026-10-21 实证：用完物品后服务端只回一条 **17 字节的差值包**
            #   （`1b 01 1e00 13010000 00100000 00 ffffffff`），里面**没有数量字段**
            #   —— 对比同槽位的 112 字节全量（`03 01 1e00 … ec57 0200 …`）可知
            #   [4:8] 不是数量。而主动发 0x76 请求全量，服务端**也不回**
            #   （20:44/20:48 两次日志都没有后续 0x613 112 字节帧）。
            #   所以数量只能**本地自减**：使用成功是确定的，减一是安全的，
            #   下一次进世界 / 手动重读拿到 112 全量时会自动校准回来。
            key = (int(cont), int(slot))
            v = self.bag.get(key)
            if v and int(v.get('iid') or 0) == int(iid):
                n = int(v.get('n') or 0) - 1
                if n <= 0:
                    self.bag.pop(key, None)
                else:
                    v['n'] = n
                self._bag_dirty = True
                self._bag_t = time.time()      # 0.4 秒后推给界面
            return True
        except Exception as ex:
            self.log('[!] 使用物品失败：%s' % ex)
            return False

    def start_use_until_empty(self, slot, iid, cont=1):
        """循环使用，直到这件物品数量归零（或到 300 次上限）

        ★ 由 `_tick` 每 1 秒发一次 —— 放 tick 里而不是起线程，是因为只有
          这条线程能安全写 socket（和心跳/打怪抢 socket 会乱序）。
          数量靠服务端回下发的 0x613 更新，数到 0 就自动停。
        """
        self._use_loop = {'slot': int(slot), 'iid': int(iid),
                          'cont': int(cont), 't': 0.0, 'n': 0}
        self.log('   [物品] 开始循环使用 槽位%d 物品%d，直到用完' % (slot, iid))

    def _use_loop_tick(self):
        """由 _tick 调用：驱动「用完为止」"""
        L = self._use_loop
        if not L:
            return
        if self.w is None:
            self._use_loop = None
            return
        # 从背包里找这件物品的当前数量（同槽位同 ID）
        cur = None
        for (_c, _s), v in self.bag.items():
            if _s == L['slot'] and int(v.get('iid') or 0) == L['iid']:
                cur = v
                break
        n = int((cur or {}).get('n') or 0)
        if cur is None or n <= 0:
            self.log('   [物品] 已用完：槽位%d 物品%d（共发 %d 次）'
                     % (L['slot'], L['iid'], L['n']))
            self._use_loop = None
            return
        if L['n'] >= 300:
            self.log('   [物品] 循环使用到 300 次上限，自动停止')
            self._use_loop = None
            return
        now = time.time()
        if now - L['t'] < 1.0:
            return
        L['t'] = now
        L['n'] += 1
        if not self.use_item(L['slot'], L['iid'], L['cont']):
            self._use_loop = None

    def do_bag_refresh(self):
        """重新读一次背包

        ★ 2026-10-21：UI 右键「重新读取背包」走这里。
          0x411 s_nCS_PlayerItemOperation 是录制里客户端进世界后真实发过的包
          （8 字节：76 00 00 00 00 00 00 00），发完服务端会重新下发整包 0x613。
        """
        if self.w is None:
            self.log('[!] 不在世界中，读不到背包')
            return
        try:
            # ★★ 2026-10-21 修：以前这里先 `self.bag.clear()`。
            #   但实测（20:44 / 20:48 两次日志）发 0x76 之后服务端**根本不回**
            #   0x613 全量 —— 清空等于把已知数据全丢了，界面上就变成"数量不对
            #   或者干脆空"。所以现在**不清**，只发请求；真有数据回来会覆盖。
            self._bag_t = 0.0
            self._bag_seen = 0
            self.w.sendall(wframe(0x411,
                                  b'\x76\x00\x00\x00\x00\x00\x00\x00'))
            self.log('   [背包] 已请求重读（0x411）—— 注意：服务端通常不回这个包，'
                     '数量以进世界时那份全量为准')
        except Exception as ex:
            self.log('[!] 请求背包失败：%s' % ex)

    # ---------------- ⑦ 技能探测：让服务端告诉我们哪个 ID 真能用
    def do_sweep(self):
        """把已学技能一个一个试，看谁真能放

        ★★★ 2026-10-20 第二次修正（上一版测出来的结果是废的）
        ------------------------------------------------------------
        上一版有三个致命毛病，难怪 17 个只「成功」了 3 个：

        ① **把所有技能都发给自己**（目标=角色ID）。
           `SkillTarget=1` 的攻击技能（1002/1003/7101/7062…）这样发，
           服务端根本不知道打谁 —— 必须给真实怪物实体ID。
        ② **间隔只有 0.9 秒**。第一个 1005 成功后服务端下发
           `0x648 整组CD初始化 1500ms`，后面 14 个全撞在公共CD里被静默丢弃。
           现在间隔 ≥2.5 秒，且每个技能发之前检查 0x648 的冷却。
        ③ **失败也记成 HIDDEN**。整组CD造成的假阴性会把好技能永久藏掉。
           现在只有「确实发出去且等足时间还没回应」才算失败，且不自动隐藏。

        修完之后，成功与否取决于** cast_profile 分流的发包档案**：
          自我施法（SELFCAST）→ 目标填自己、step=5、组=391
          打怪类               → 必须挑最近的活怪，且距离在射程内，step=6、组=392
          ⚠ HavetoEquip=1 **完全不拦**（2026-10-20 抓包实证 + 19:3x 按用户要求
            取消「需装备」提示）：7002 伤痛咒 equip=1，服务端照样回 5 次 0x60A。
            早年「7xxx 全灭是因为需装备」的判断是错的，真因是 step 发错了。
        """
        if not self.in_world or self.w is None:
            self.log('[!] 试技能失败：当前不在世界中')
            self.ev.put(('sweep_res', {'ok': False, 'msg': '未进入世界'}))
            return
        cid = (self.picked_cid or 0) & 0xFFFFFFFF
        if not cid:
            self.ev.put(('sweep_res', {'ok': False, 'msg': '无角色ID'}))
            return
        ids = sorted(self.learned) or sorted(COMMON_SKILLS)
        if not ids:
            self.ev.put(('sweep_res', {'ok': False, 'msg': '服务端还没下发已学技能'}))
            return
        self.skill_ack_ids.clear()
        self.sweep = {'ids': ids, 'i': -1, 'ok': [], 'bad': [],
                      'cur': 0, 'sent': 0.0, 't': 0.0, 'tgt': 0}
        self.log('   [试技能] 开始：%d 个已学技能' % len(ids))
        # ★★★ 2026-10-20 按 cast_profile 分流，把「目标怎么给」提前说清。
        #   ⚠ 不再提「需装备」—— 抓包实证服务端不校验装备（7002 需装备仍回
        #      5 次 0x60A），该提示已于 19:3x 按用户要求取消。
        _no = [s for s in ids if cast_profile(s)[0]]
        _ne = [s for s in ids if not cast_profile(s)[0]]

        def _fmt(lst):
            out = []
            for s in lst:
                c = skill_cfg(s) or {}
                out.append('%d·%s' % (s, c.get('name') or '?'))
            return '  '.join(out) or '无'

        if _no:
            self.log('   [试技能] ○ 自我施法（目标填自己/step5/组391）%d 个：%s'
                     % (len(_no), _fmt(_no)))
        if _ne:
            self.log('   [试技能] ⊙ 打怪类（目标填怪/step6/组392）%d 个：%s'
                     % (len(_ne), _fmt(_ne)))
        self.log('   [试技能] 每发之间隔 %d 秒，等公共CD(1500ms)过去' % SWEEP_GAP)
        self.ev.put(('sweep_res', {'ok': True, 'msg': '开始', 'n': len(ids),
                                   'skip_eq': 0}))

    def _sweep_pick_target(self):
        """给「需要目标」的技能挑一只活怪：在射程内、最近的

        返回 (eid, name, dist)；没有就 (0, '', -1)
        """
        ns = [t for t in self._npc_list() if t[0] >= 0]
        return (ns[0][2], ns[0][1], ns[0][0]) if ns else (0, '', -1.0)

    def _sweep_step(self):
        """「试一遍」状态机（由 _tick 驱动，不阻塞收包）"""
        w = self.sweep
        if not w or not self.in_world or self.w is None:
            return
        cid = (self.picked_cid or 0) & 0xFFFFFFFF
        if not cid:
            self.sweep = None
            return
        now = time.time()
        if w['cur']:
            if now - w['sent'] < SWEEP_WAIT:
                return
            sid = w['cur']
            _nm = (skill_cfg(sid) or {}).get('name') or ''
            if sid in self.skill_ack_ids:
                w['ok'].append(sid)
                VERIFIED.add(sid)
                HIDDEN.discard(sid)
                self.log('   [试技能] %d %s ✓ 能放（组 %d）'
                         % (sid, _nm, group_of(sid)))
            else:
                w['bad'].append(sid)
                _cfg = skill_cfg(sid) or {}
                _why = ''
                if not _cfg.get('nosel') and w.get('tgt') == cid:
                    _why = ' —— 这技能要目标，但附近没怪'
                self.log('   [试技能] %d %s × 没反应（组 %d）%s'
                         % (sid, _nm, group_of(sid), _why))
            w['cur'] = 0
            w['t'] = now + SWEEP_GAP
            return
        if now < w['t']:
            return                      # 两招之间留足间隔，别撞公共CD
        w['i'] += 1
        if w['i'] >= len(w['ids']):
            self.sweep = None
            # ★ 不再自动 HIDDEN —— 试出来的「没反应」可能是CD/距离造成的，
            #   隐藏了会连带把本来能放的技能也藏掉（用户之前就中过这个）
            save_state()
            self.log('   [试技能] 完成：能放 %d 个 / 没反应 %d 个'
                     % (len(w['ok']), len(w['bad'])))
            if w['ok']:
                self.log('   [试技能] ★ 能放：%s'
                         % ' '.join('%d' % s for s in w['ok']))
            if w['bad']:
                self.log('   [试技能] × 没反应：%s（不自动隐藏，可再试一次）'
                         % ' '.join('%d' % s for s in w['bad']))
            self.ev.put(('sweep_res', {'ok': True, 'done': True,
                                       'good': w['ok'], 'bad': w['bad']}))
            return
        sid = w['ids'][w['i']]
        cfg = skill_cfg(sid) or {}
        # ★ 2026-10-20 按 cast_profile 分流（真包实证）：
        #   自我施法（SELFCAST）→ 目标自己、step=5、组=391、不发 0x43D
        #   其余（含 SkillTarget=0 的 7002/7361，真客户端是当怪放的）→ 目标怪、step=6
        #   ⚠ HavetoEquip=1 不拦（录制实证 7002 需装备仍能放 5 次）
        _self, _stp, _grp = cast_profile(sid)
        g, st = _grp, _stp
        if _self:
            tgt = cid
            _tname = '(自己)'
        else:
            tgt, _tn, _td = self._sweep_pick_target()
            if not tgt:
                if cfg.get('nosel'):
                    tgt = cid                  # 没怪时自我施法类兜底填自己
                    _tname = '(自己·兜底)'
                else:
                    self.log('   [试技能] %d %s 跳过 —— 这技能要目标，附近没怪'
                             % (sid, cfg.get('name') or ''))
                    w['bad'].append(sid)
                    w['t'] = now              # 跳过的不占额外时间
                    return
            else:
                _tname = '%s(%.1fm)' % (_tn, _td)
                # 需要目标的技能，先锁目标再放（真客户端是两步）
                try:
                    self.w.sendall(wframe(0x43D, struct.pack('<II', cid, tgt)))
                except Exception:
                    pass
        w['tgt'] = tgt
        try:
            self.w.sendall(wframe(0x408, struct.pack(
                '<9I', cid, sid & 0xFFFFFFFF, 0, 0,
                g & 0xFFFFFFFF, st & 0xFFFFFFFF,
                tgt, ATTACK_ARG7, ATTACK_TAIL)))
        except Exception as ex:
            self.log('[!] 试技能发送失败：%s' % ex)
            self.sweep = None
            self.ev.put(('sweep_res', {'ok': False, 'msg': str(ex)}))
            return
        self.log('   [试技能] → %d %s 组 %d step %d 目标 %s'
                 % (sid, cfg.get('name') or '', g, st, _tname))
        w['cur'] = sid
        w['sent'] = now

    def _nearest_target(self):
        for t in self._npc_list():
            if t[0] >= 0:
                return t[2], t[1], t[0]
        return 0, '', -1.0

    def do_probe(self, kw, group=None, step=None):
        """按技能名（或 ID）探测：同名的每个等级 ID 都发给服务端试一次

        同名技能有十几个 ID（伤痛咒 2001~2039），只有学会的才受理。
        服务端受理了会回 0x648，据此把能用的挑出来。
        """
        if not self.in_world or self.w is None:
            self.log('[!] 探测失败：当前不在世界中')
            self.ev.put(('probe_res', {'ok': [], 'msg': '未进入世界'}))
            return
        kw = (kw or '').strip()
        ids = [sid for sid in sorted(SKILL_DB)
               if kw and kw in SKILL_DB[sid]['name']]
        if not ids and kw.isdigit():
            ids = [int(kw)]
        # ★★★ 只探测「已学」的 —— 没学的发了服务端必然不理，白白浪费时间
        pool = self.learned
        if pool:
            keep = [x for x in ids if x in pool]
            if keep:
                ids = keep
            elif not ids:
                ids = sorted(pool)
            else:
                self.log('   [!] 名字含「%s」的 %d 个技能角色都没学，'
                         '跳过（已学的 %d 个：%s）'
                         % (kw, len(ids), len(pool),
                            ' '.join(str(x) for x in sorted(pool))))
                self.ev.put(('probe_res', {'ok': [], 'msg': '未学会'}))
                return
        if not ids:
            self.log('[!] 探测失败：没有名字里含「%s」的技能' % kw)
            self.ev.put(('probe_res', {'ok': [], 'msg': '没有匹配技能'}))
            return
        eid, nm, d = self._nearest_target()
        if not eid:
            self.log('[!] 探测失败：附近没有怪 —— 站到怪旁边再探测')
            self.ev.put(('probe_res', {'ok': [], 'msg': '附近没有怪'}))
            return
        # ★★★ 2026-10-20 终极定案：组值 392 / step 6 是全场常量，
        #   不跟技能走（15 帧真 0x408 实测，技能 7002/7062/1003 混发都是这两个值）。
        #   以前这里的「组 = 技能自己的 SkillNameID-1000」是错的 —— 那套数字
        #   服务端从来不认，包括「探测永远报一个都没受理」也是这个原因。
        self.skill_ack_ids.clear()       # 清掉旧的，免得把上一次的受理算进来
        self.probe = {'kw': kw, 'ids': ids, 'i': 0, 'ok': [],
                      'cur': 0, 'sent': 0.0, 'gap_t': 0.0, 'eid': eid,
                      'sel': False,
                      'tried': {}}        # 每个 ID 到底能不能用
        self.log('   [探测] 开始：名字含「%s」共 %d 个 ID，目标 %s（%.1f m）'
                 % (kw, len(ids), nm, d))
        self.log('   [探测] 按 cast_profile 取组/step（自我施法=391/5，攻击=392/6）：%s'
                 % '  '.join('%d→%s' % (x, '自己/391/5' if cast_profile(x)[0]
                                        else '怪/392/6')
                            for x in ids[:8]))

    def _probe_step(self):
        """探测状态机（由 _tick 驱动，不阻塞收包）"""
        p = self.probe
        if not p or not self.in_world or self.w is None:
            return
        now = time.time()
        if p['cur']:
            if now - p['sent'] < PROBE_WAIT:
                return
            cid = p['cur']
            if cid in self.skill_ack_ids:
                p['tried'][cid] = True
                if cid not in p['ok']:
                    p['ok'].append(cid)
                VERIFIED.add(cid)
                self.log('   [探测] %d ✓ 服务端受理' % cid)
            else:
                # 这一组没反应，但别的组可能行 —— 先记着，别急着判死
                p['tried'].setdefault(cid, False)
                self.log('   [探测] %d × 没反应' % cid)
            p['cur'] = 0
            p['gap_t'] = now + PROBE_GAP
            return
        if now < p['gap_t']:
            return
        if p['i'] >= len(p['ids']):
            ok = p['ok']
            self.probe = None
            # ★ 把「确认不能用」的从列表里去掉（只在这个名字下至少有一个能用时才敢判）
            bad = [k for k, v in p['tried'].items() if not v]
            if ok and bad:
                HIDDEN.update(bad)
                save_state()
                self.log('   [探测] 已从技能列表里隐藏 %d 个用不了的 ID：%s'
                         % (len(bad), ' '.join(str(x) for x in sorted(bad))))
            if ok:
                self.log('   [探测] 完成：可用 %s'
                         % ' / '.join('%d(组%d)' % (x, group_of(x)) for x in ok))
            else:
                self.log('   [探测] 完成：%d 个 ID 一个都没受理 —— '
                         '多半是这个技能真没学会，或者当前状态/朝向不允许。'
                         '（一个都没成功，所以什么都没隐藏）' % len(p['ids']))
            _sc, _stp0, _grp0 = (cast_profile(ok[0]) if ok
                                 else (False, DEFAULT_STEP, 0))
            self.ev.put(('probe_res', {'ok': ok, 'kw': p['kw'],
                                       'group': _grp0 if ok else 0,
                                       'step': _stp0}))
            return
        sid = p['ids'][p['i']]
        p['i'] += 1
        # ★ 按 cast_profile 取（2026-10-20 真包定案）：
        #   自我施法 = 391/5/自己；攻击 = 392/6/怪。
        #   ⚠ 以前这里恒发 392/6，自我施法类探测永远「没反应」。
        _self, _stp, _grp = cast_profile(sid)
        g, st = _grp, _stp
        cid_me = (self.picked_cid or 0) & 0xFFFFFFFF
        _tgt = cid_me if _self else (p['eid'] & 0xFFFFFFFF)
        try:
            if not p['sel'] and not _self:    # 选中目标只发一次
                p['sel'] = True
                self.w.sendall(wframe(0x43D, struct.pack(
                    '<II', cid_me, p['eid'] & 0xFFFFFFFF)))
            self.w.sendall(wframe(0x408, struct.pack(
                '<9I', cid_me, sid & 0xFFFFFFFF, 0, 0,
                g & 0xFFFFFFFF, st & 0xFFFFFFFF,
                _tgt, ATTACK_ARG7, ATTACK_TAIL)))
        except Exception as ex:
            self.log('[!] 探测发送失败：%s' % ex)
            self.probe = None
            self.ev.put(('probe_res', {'ok': p['ok'], 'msg': str(ex)}))
            return
        p['cur'] = sid
        p['sent'] = now

    def _auto_atk_step(self):
        """自动打怪推进（由 _tick 调）

        ★ 2026-10-20 多选版：攻击格可多选，点「开始」后**按格子顺序轮流放**，
          某一招在冷却/没蓝/前置不满足就**跳过试下一个**，全被跳过才停。
          没有多选（连招为空）就只放单个技能。
          每一招的间隔取 max(吟唱时间 + 余量, 全局最小间隔)，
          并且每一招各自受 0x648 下发的 CD 约束。
        """
        if not self.auto_atk or (not self.auto_atk_skill and not self.combo):
            return
        if not self.in_world or not self.scene['done']:
            return
        now = time.time()
        if now < self.combo_t:
            return
        if now - self.last_atk_t < max(ATTACK_MIN_GAP, 0.8):
            return
        # ★★★ 按顺序挑第一个「发得出去」的技能：
        #   _cast_block 非空 = 冷却/没蓝/没血/前置不满足/已死 → 跳过试下一个。
        #   以前是碰到第一个被拦的就直接 return，用户就会看到「选中了 5 个
        #   技能，只有一个在转」—— 现在轮着来，冷却中的自动让位。
        if self.combo:
            _n = len(self.combo)
            sk = g = st = None
            _last_blk = ''
            for _k in range(_n):
                _s, _g, _st = self.combo[(self.combo_i + _k) % _n]
                _blk = self._cast_block(_s)
                if not _blk:
                    sk, g, st = _s, _g, _st
                    self.combo_i = (self.combo_i + _k) % _n   # 停在这一招，放完 +1
                    break
                _last_blk = _blk
            if sk is None:
                # 全被跳过：每 5 秒把最后一个原因念一次（带数字的人话）
                if _last_blk and now - getattr(self, '_mp_hint_t', 0.0) > 5.0:
                    self._mp_hint_t = now
                    self.log('   [自动] %s' % _last_blk)
                return
        else:
            sk, g, st = self.auto_atk_skill
            # ★★★ 2026-10-20 19:xx 统一「发得出去吗」检查（_cast_block）：
            #   冷却 / 没蓝 / 没血 / 前置不满足 / 已死，全浓缩成一句带数字的人话。
            #   用户实测反馈「用一次就放不出来」，八成就是这些原因。
            #   以前只默默跳过不吭声，用户以为软件坏了。现在每 5 秒把现状念一次。
            _blk = self._cast_block(sk)
            if _blk:
                if now - getattr(self, '_mp_hint_t', 0.0) > 5.0:
                    self._mp_hint_t = now
                    self.log('   [自动] %s' % _blk)
                return
        ns = self._npc_list()
        if not ns:
            self._no_target(now, '列表里一只怪都没有')
            return
        # ★ 射程过滤：技能配置里的 Range_Max 单位是 1/100 米（1500 = 15 米）。
        #   超出射程就空放，服务端也不会算伤害，白费一轮 CD。
        cfg = skill_cfg(sk)
        rng = (cfg['rng'] / 100.0) if cfg else 0.0
        if rng > 0:
            inr = [t for t in ns if 0 <= t[0] <= rng]
            if not inr:
                # ★★ 修「新刷出来的怪打不了」：新怪常常只有身份包（0x6B9），
                #   绝对坐标还没到，距离算出来是 -1。原来 `0 <= t[0]` 一刀切
                #   把它们全滤掉 —— 于是怪明明在列表里，就是不打它。
                #   现在：确认在射程内的优先；一个都没有时，把「距离未知」的
                #   也算进来赌一把（它们本来就在筛选半径内）。
                unk = [t for t in ns if t[0] < 0]
                if unk:
                    inr = unk
                    if time.time() - getattr(self, '_hint_t', 0) > 8.0:
                        self._hint_t = time.time()
                        self.log('   [自动] %d 只怪还没拿到坐标（%s），'
                                 '先按在射程内打'
                                 % (len(unk), unk[0][1]))
                else:
                    if time.time() - getattr(self, '_hint_t', 0) > 8.0:
                        self._hint_t = time.time()
                        self.log('   [自动] 射程内没有怪（最近 %s 在 %.1f m，'
                                 '技能 %d 射程 %.1f m）—— 走近点或换远程技能'
                                 % (ns[0][1], ns[0][0], sk, rng))
                    self._no_target(now, '射程内没有怪')
                    return
            ns = inr
        # ★★★ 2026-10-20 修「新刷出来的怪打不了」：
        #
        #   原来的写法有两个坑：
        #     ① `eid = ns[0][2]` 先当成默认值 —— ns[0] 是**最近**的那个，
        #        但它可能是「未知/待定」类实体（名字没解析出来、或是别的玩家/宠物）。
        #        对着这种东西发 0x408，服务端判断不了是敌对单位，直接丢弃。
        #     ② 找真怪用的是 `for ... else` + `break`，只在「当前锁定目标没了」
        #        时才走一遍；而「真怪」过滤和「距离最近」两套排序混在一起，
        #        换目标时就容易挑到离得近但打不了的实体。
        #
        #   现在明确三级优先：
        #     1) 当前锁定的目标还活着且在射程内 → 继续打它（不来回切，省 0x43D）
        #     2) 否则：**只在 kind=='怪' 里**挑最近的
        #     3) 一只真怪都没有 → 才退到最近的「待定/未知」（赌一把），
        #        但日志提示一次，别让用户以为程序卡了
        # ★★★ 2026-10-20 22:3x 实机日志修正「附近有怪不攻击」：
        #
        #   旧逻辑第一条是「当前锁定目标优先」**不看类型**，于是锁在一个
        #   0.3 米外的「未知」实体（别人的召唤兽/宠物）上，之后每 12 秒
        #   都往它身上放技能（日志 #60/#70/…/#110 全是同一个 0x0263b76d），
        #   旁边真正的平原草羊一次都没被选中。
        #   → 锁定只在「它是认得出的怪」时才生效，其余一律重新挑最近的怪。
        eid = 0
        if self.atk_target:
            o = self.ent.get(self.atk_target) or {}
            if self._ent_kind(o) == '怪' and any(t[2] == self.atk_target
                                                for t in ns):
                eid = self.atk_target          # 1) 锁定目标（必须真是怪）
        if not eid:                            # 2) 真怪里挑最近的
            for t in ns:
                if t[5] == '怪':
                    eid = t[2]
                    break
        if not eid:                            # 3) 退到「待定」
            for t in ns:
                if t[5] == '待定':
                    eid = t[2]
                    break
        if not eid:                            # 4) 最后才试「未知」（可能身份还没解析）
            eid = ns[0][2]
            if time.time() - self._hint_t > 8.0:
                self._hint_t = time.time()
                self.log('   [自动] 射程内没有认得出的怪（最近 %s 是「%s」），'
                         '先试着打它' % (ns[0][1], ns[0][5] or '未知'))
        if self.do_attack(eid=eid, skill=sk, group=g, step=st, auto=True):
            self._nofind_t = 0.0            # 打到了 → 清掉「找不到目标」的计时
            if self.combo:
                # 下一招：按这一招的吟唱时间排队（配置里没写就 0.8 秒）
                cast = (cfg['cast'] / 1000.0) if cfg else 0.0
                self.combo_t = time.time() + max(ATTACK_MIN_GAP, cast + 0.35)
                self.combo_i = (self.combo_i + 1) % len(self.combo)

    def _no_target(self, now, why):
        """开着自动打怪却一直没东西可打（2026-10-20「刷新不及时」）

        连续 AOI_HARD_SEC 秒找不到目标 → **重拉整张实体清单**（清台账）。
        服务端只在 AOI 握手后推一次完整清单，站桩久了新刷的怪很可能根本没推
        过来；轻刷新要等 8 秒一轮，这里再兜一层。
        """
        if not self._nofind_t:
            self._nofind_t = now
            return
        if now - self._nofind_t < AOI_HARD_SEC:
            return
        self._nofind_t = now
        self._resync_scene(clear=True)
        self.log('   [自动] %.0f 秒没打到东西（%s）—— 已重新拉取周围实体'
                 % (AOI_HARD_SEC, why))

    # ---------------- ⑤ 自身血量 / 复活
    RELIVE_TYPES = (1, 3, 0)        # 0x40f 的复活类型候选（反编译里见过 1 和 3）

    def _bag_push(self):
        """把背包里的**指定物品**推给界面

        ★★★ 2026-10-21 用户定案：**只认 `刷阵宝箱ID.txt` 里列的物品ID**，
          别的什么都不读 —— 不再按名字猜箱子、不再兜底铺前几件。

          `刷阵宝箱ID.txt` 格式：每行一个物品ID（也接受逗号/空格/顿号分隔）。
          文件为空 → 背包框就是空的，并在日志里提示去填。

        ★ 数据到达是「逐槽位连发」的（几十帧挤在 0.2 秒内），所以收到帧只置
          `_bag_dirty`，由 `_tick` 在「距最后一帧 ≥0.4 秒」时统一推一次完整的
          —— 不能像以前那样「距上次推送不足 0.5 秒就 return 丢掉」，
          那样只有第一帧会显示出来。
        """
        self._bag_dirty = False
        boxes = []
        total = 0
        want = box_id_set()
        # 容器 1（主背包）排最前，其余容器按号码排后面
        _items = sorted(self.bag.items(),
                        key=lambda kv: (kv[0][0] != 1, kv[0][0], kv[0][1]))
        try:
            for (_c, _s), v in _items:
                iid = int(v.get('iid') or 0)
                if not iid:
                    continue
                total += 1
                if iid not in want:
                    continue
                boxes.append({'iid': iid, 'n': int(v.get('n') or 0),
                              'slot': _s, 'cont': _c, 'name': item_name(iid)})
        except Exception:
            boxes = []
        if not want:
            self.log('[!] 刷阵宝箱ID.txt 里没有物品ID —— 背包框不显示任何物品。'
                     '把要显示的物品ID填进去（一行一个），重新上线即生效')
        else:
            self.log('   [背包] 背包共 %d 件，其中指定的 %d 个在包里'
                     '（指定名单 %d 个，显示前 %d 个）'
                     % (total, len(boxes), len(want),
                        min(len(boxes), N_ITEM_SLOT)))
            for _b in boxes[:N_ITEM_SLOT]:
                _iid = int(_b.get('iid') or 0)
                self.log('   [背包]   · 物品%-6d %-16s ×%-4d'
                         % (_iid, item_name(_iid) or '(无名字)',
                            int(_b.get('n') or 0)))
        # ★ 一律截到 6 条再推：界面只有 6 格，多传没意义，还会让日志说"全显示了"
        self.ev.put(('bag_box', boxes[:N_ITEM_SLOT]))

    def _note_lv(self, cid, lv, exp=None, need=None):
        """收到等级/经验更新（0x60F 或 0x623 attr 5001/3009）

        ★ 只认**自己**的：0x60F 也会广播队友的（录制里 24 条全是队友 cid），
          把别人的等级显示到自己身上就闹笑话了。
        """
        me = (self.picked_cid or 0) & 0xFFFFFFFF
        if me and cid and int(cid) != me:
            return
        changed = False
        if lv:
            lv = int(lv)
            if lv != self.level:
                self.level = lv
                changed = True
        if exp is not None:
            exp = int(exp)
            if exp != self.exp:
                self.exp = exp
                changed = True
        if need is not None:
            need = int(need)
            if need != self.exp_need:
                self.exp_need = need
                changed = True
        if changed:
            self.ev.put(('self_lv', {'lv': self.level, 'exp': self.exp,
                                     'need': self.exp_need}))

    def _note_self_attr(self, attr, val):
        """0x623 里属于自己的一条：[实体][属性ID][属性值]

        真录制实测（5647 帧全部 12 字节）：
            3001 = 当前血量      2008 = 血量上限
            3002 = 当前法力      2009 = 法力上限
        ⚠ 以前把「属性ID」当成血量直接用，再配一个「>2500 就算上限」的猜测，
          所以界面上的血量一直是鬼数字。属性ID 和血量是两个字段，不能混。
        ★ 2026-10-20 19:xx：顺手自学「每一招耗多少蓝/血」—— 血祭是烧血的
          （实测 −261 血 / +260 蓝），只学血不够永远判断不出来。
          配置表 123 列里没有能确认的消耗列，但服务端每次扣都会发 0x623，
          记下「上一次施法之后掉多少」关联到那一招，多学几次取最大值。
        """
        self.hp_t = time.time()
        # ★★ 2026-10-21 诊断：用户报「蓝/等级/经验都不读，只有血条准」——
        #   每个属性 ID **第一次**出现时打一行，一次上线就能看清服务端到底推了哪些。
        if attr not in self._attr_seen:
            self._attr_seen[attr] = val
            self.log('   [属性] 首次收到 attr %-5d = %s' % (attr, val))
        _last = getattr(self, '_last_cast_sk', 0)
        _fresh = time.time() - getattr(self, '_last_cast_t', 0.0) < 3.0
        if attr == 3001:
            if (_last and self.hp is not None and val < self.hp and _fresh):
                _d = self.hp - val
                if 0 < _d < 100000:
                    self._skill_hp_cost[_last] = max(
                        self._skill_hp_cost.get(_last, 0), _d)
            self.hp = val
            if val <= 0:
                if not self.dead:
                    self.dead = True
                    self.summon_t.clear()       # 死了召唤物也没了
                    self.log('[!] 角色已经死亡（0x623 血量=0）—— 位置会失效，'
                             '点「复活」或重新传送一次')
                self.ev.put(('self_hp', {'hp': 0, 'max': self.hp_max,
                                         'mp': self.mp, 'mp_max': self.mp_max,
                                         'dead': True}))
                return
            if self.dead:
                self.dead = False
        elif attr == 2008:
            self.hp_max = val
            # 上限一到就知道满血是多少；当前血量还没来时先按满血显示
            if self.hp is None:
                self.hp = val
        elif attr == 3002:
            # 自学耗蓝：只学下降量（忽略回蓝/升级导致的上涨）
            _prev = self.mp
            if (_prev is not None and _last and val < _prev and _fresh):
                _d = _prev - val
                if 0 < _d < 100000:
                    self._skill_mp_cost[_last] = max(
                        self._skill_mp_cost.get(_last, 0), _d)
            self.mp = val
            if val > self._mp_seen_max:
                self._mp_seen_max = val
            self.ev.put(('self_hp', {'hp': self.hp, 'max': self.hp_max,
                                     'mp': self.mp, 'mp_max': self.mp_max,
                                     'dead': self.dead}))
            # ★ 2026-10-21：蓝量变化也是「低血蓝自动凝神术」的触发点
            #   （3002 只在耗蓝时发，这里不检查就永远等不到）
            self._auto_heal_check()
            return
        elif attr == 2009:
            self.mp_max = val
            # ★ 2026-10-21：上限到了也刷一次界面 —— 有些角色只推上限不推当前值，
            #   以前这里不推事件，蓝条就一直是「—」。
            self.ev.put(('self_hp', {'hp': self.hp, 'max': self.hp_max,
                                     'mp': self.mp, 'mp_max': self.mp_max,
                                     'dead': self.dead}))
        elif attr == 5001:
            # ★ 2026-10-21：attr 5001 = 等级（录制里 12/23/24/27/28… 与 0x60F 的
            #   pl[4] 完全对应）。0x60F 有时不推自己，这里是兜底来源。
            self._note_lv(self.picked_cid or 0, val)
            return
        elif attr == 3009:
            # ★ attr 3009 = 当前经验（连续递增，和 0x60F 的 [16:20] 同值）
            self._note_lv(self.picked_cid or 0, 0, val)
            return
        else:
            return
        # 上限没下发过就先用见过的最大值兜底（登录时一般就是满血）
        if self.hp is not None:
            if self.hp_max is None or (self.hp > self.hp_max):
                self.hp_max = self.hp
        self.ev.put(('self_hp', {'hp': self.hp, 'max': self.hp_max,
                                 'mp': self.mp, 'mp_max': self.mp_max,
                                 'dead': self.dead}))
        self._auto_heal_check()          # ★ 血/上限变化 → 评一次要不要放凝神术

    def _note_self_hp(self, hp, state):
        """兼容旧调用：把单个数值当作「当前血量」处理"""
        self._note_self_attr(3001, hp)

    def _send_relive(self, kind):
        cid = (self.picked_cid or 0) & 0xFFFFFFFF
        # 0x40f s_nCS_PlayerRelive：21 字节 = [u32 角色ID][u8 复活类型][16 字节填充]
        body = struct.pack('<IB', cid, kind & 0xFF) + b'\x00' * 16
        assert len(body) == 21
        self.w.sendall(wframe(0x40F, body))
        self.log('   → 已发送复活 0x40f（类型 %d，21 字节）' % kind)

    def do_relive(self):
        if not self.in_world or self.w is None:
            self.log('[!] 复活失败：当前不在世界中')
            self.ev.put(('relive_res', {'ok': False, 'msg': '未进入世界'}))
            return
        if not self.dead:
            self.log('   还活着（血量 %s/%s），不用复活'
                     % (self.hp, self.hp_max))
            self.ev.put(('relive_res', {'ok': False, 'msg': '角色没死'}))
            return
        self._relive_pending = True
        self.relive_try = 0
        self.relive_last = 0.0          # 下一 tick 立刻发第一条
        self.log('   开始尝试复活：依次试类型 %s，收到 0x646 即成功'
                 % (self.RELIVE_TYPES,))

    # ---------------- ⑤2 技能收录
    def _note_learned(self, pl):
        """0x625 s_nSC_InitPlayerSkill: [u32 角色][u16 数量][u32 技能ID × N]

        ★★★ 这是「哪些技能真能放」的唯一权威来源。以前没有这一条，
        所以挂机端只能拿 480 条全表盲试，发的 ID 角色没学 → 服务端静默丢弃。
        """
        eid, n = struct.unpack_from('<IH', pl, 0)
        n = min(n, (len(pl) - 6) // 4)
        ids = [struct.unpack_from('<I', pl, 6 + i * 4)[0] for i in range(n)]
        # ★ 只认自己这个角色的（别人的角色下发也忽略）
        me = self.picked_cid or 0
        if me and eid != me:
            return
        # ★★★ 2026-10-21 多开：**不再覆盖模块级 LEARNED**
        #   以前这里写 global LEARNED = 这个角色的技能，多角色同时在线时
        #   后登录的会盖掉前面的 —— A 角色的技能格列表突然变成 B 的。
        #   现在只写实例上的 self.learned，屏幕上用哪个角色就取哪份。
        self.learned = set(ids)
        self.learned_cid = eid
        # 只在内容变了的时候打日志，免得重复刷
        sig = tuple(sorted(ids))
        if sig == getattr(self, '_learned_sig', None):
            return
        self._learned_sig = sig
        names = []
        for sid in sorted(ids):
            cfg = SKILL_DB.get(sid)
            names.append('%d·%s' % (sid, cfg['name'] if cfg else '?'))
        self.log('   ★★★ 已学技能（0x625）：角色 0x%08x 下发 %d 条 / 去重 %d 个 —— %s'
                 % (eid, n, len(set(ids)), '  '.join(names)))
        # ★ 顺手把默认技能改成一个「真学会了」的，避免拿没学的 ID 空放
        if self.auto_atk_skill and self.auto_atk_skill[0] not in self.learned:
            self.log('   [!] 当前自动打怪技能 %d 不在已学列表里 —— 已自动换成 %d'
                     % (self.auto_atk_skill[0], self._pick_default_skill()))
        self.ev.put(('learned', {'ids': sorted(ids), 'cid': eid}))

    def _pick_default_skill(self):
        """从已学技能里挑一个最像「攻击技能」的做默认

        优先 7000 段（巫士伤害技）→ 1000 段（冲击一类）→ 其余；
        明确排除 20006 回城 / 20071 这类非攻击技能。
        """
        pool = [s for s in self.learned
                if s not in (20006, 20071, 20019, 3001)]
        if not pool:
            return DEFAULT_SKILL
        # 真录制里客户端一直在用的就是 7002 伤痛咒，优先它
        if DEFAULT_SKILL in pool:
            return DEFAULT_SKILL
        def rank(s):
            cfg = SKILL_DB.get(s) or {}
            rng = cfg.get('rng') or 0
            # 伤害技一般「有射程、有吟唱」；回城类没有
            return (0 if 4000 < s < 8000 else 1, 0 if rng else 1, s)
        return sorted(pool, key=rank)[0]

    def _note_skill_ack(self, pl):
        """0x648 s_nSC_SkillCDGroupInit

        真录制 20 字节 = 5×u32，字段实测：
            [0]=0x10 恒定（协议版本/类型标记，不是角色）
            [1]=角色ID
            [2]=技能ID（**0 表示整组 CD 初始化，不是某个技能**）
            [3]=CD 毫秒
            [4]=CD 毫秒（与 [3] 相同）
        真包例子：
            10000000 2b070000 00000000 dc050000 dc050000  → 角色 1835 整组 CD=1500ms
            10000000 2b070000 6e1b0000 32000000 32000000  → 角色 1835 技能 7022 CD=50ms
        ⚠ 旧代码把 [1] 当「角色」[2] 当「技能」是对的，但没判断 [2]==0 的情况，
          会把「技能 0」记进 VERIFIED，污染技能列表。
        """
        _a, who, s, cd1, _cd2 = struct.unpack('<IIIII', pl[:20])
        self.atk_ack += 1
        self._last_ack_t = time.time()
        if not s:
            # 整组 CD 初始化，不对应具体技能 —— 只当「服务端活着」的信号
            if self._grp_cd_log < 3:
                self._grp_cd_log += 1
                self.log('   0x648 整组CD初始化：角色 0x%08x CD %dms'
                         % (who, cd1))
            # ★ 2026-10-20 新版界面：把整组 CD 也记下来，公共冷却内置灰 + 拦截
            #   （真客户端 1003/7101 连发间隔从没低于 1.3s，就是这个在管）
            if cd1:
                self.grp_cd = time.time() + max(0.3, cd1 / 1000.0 - CD_GRACE)
            return
        if who and self.picked_cid and who != self.picked_cid:
            return                            # 别人的技能
        # ★ 本地护栏 = 声明 CD − 1s 宽限（真客户端就比声明早 0.1~0.8s recast），
        #   观测过的技能（血祭）按实测间隔走。别比真客户端还严，否则用户
        #  会觉得「用一次就再也放不出来」—— 那是软件把自己勒住了。
        if cd1:
            self.skill_cd[s] = time.time() + cd_guard_sec(s, cd1)
        self.skill_seen[s] = cd1
        self.skill_ack_ids.add(s)
        VERIFIED.add(s)
        self._ack_skill = s
        self._noack_sk.pop(s, None)          # 服务端理了，清零无响应计数
        self._note_cast_ok(s)
        self.log('   ★ 服务端受理 0x648：技能 %d 冷却 %dms' % (s, cd1))
        self.ev.put(('skill_seen', {'id': s, 'cd': cd1}))

    # ---------------- ⑤ 施法成功后的状态记账（前置技能 / 无响应诊断）
    def _note_cast_ok(self, sk):
        """服务端确认放过这个技能 → 记账。

        ① 前置来源技能（野兽之魂这类）记下「在线」时刻；
        ② 清零连续无响应计数。
        """
        try:
            sk = int(sk)
        except (TypeError, ValueError):
            return
        self._noack_sk.pop(sk, None)
        if any(v[0] == sk for v in PREREQ.values()):
            self.summon_t[sk] = time.time()

    def _summon_online(self, sk):
        """前置来源技能还在线吗（放过且没超过保质期）"""
        t = self.summon_t.get(int(sk or 0)) or 0.0
        return bool(t) and (time.time() - t) < SUMMON_TTL

    def _cast_block(self, sk, want_hp=False):
        """这个技能现在发得出去吗？发不出去就返回一句人话（带数字），能发返回 None。

        检查顺序和服务端静默丢弃的原因一一对应：冷却 / 没蓝 / 没血 / 前置 / 已死。
        """
        try:
            sk = int(sk)
        except (TypeError, ValueError):
            return None
        nm = (skill_cfg(sk) or {}).get('name') or ('技能%d' % sk)
        # 已死
        if self.dead:
            return '角色已死亡 —— 先复活'
        # 整组公共CD（0x648 key=0 那 1500ms，所有技能共享）
        _gl = self.grp_cd - time.time()
        if _gl > 0:
            return '公共冷却中，还要 %.1f 秒（所有技能共享）' % _gl
        # 冷却
        left = self.skill_cd.get(sk, 0.0) - time.time()
        if left > 0:
            _stated = self.skill_seen.get(sk)
            _obs = ('（实测 %.0fs 可重放）' % OBSERVED_CD[sk]) \
                if sk in OBSERVED_CD else ''
            return '「%s」冷却中，还要 %.1f 秒%s' % (nm, left, _obs)
        # 没蓝
        if self.mp is not None and self.mp <= 0:
            return '没蓝了（当前 %s/%s）—— 打坐回蓝或换个不耗蓝的技能' % (
                self.mp, self.mp_max or self._mp_seen_max or '?')
        _mpc = self._skill_mp_cost.get(sk, 0)
        if _mpc and self.mp is not None and self.mp < _mpc:
            return '蓝不够放「%s」（当前 %d，这一招约耗 %d）' % (nm, self.mp, _mpc)
        # 没血（血祭这类烧血的）
        _hpc = self._skill_hp_cost.get(sk, 0)
        if _hpc and self.hp is not None and self.hp < _hpc:
            return '血不够放「%s」（当前 %d，这一招约耗 %d）' % (nm, self.hp, _hpc)
        # 前置状态
        _pq = prereq_of(sk)
        if _pq and not self._summon_online(_pq[0]):
            return '「%s」需要先放出%s（技能 %d）' % (nm, _pq[1], _pq[0])
        return None

    def _cast_note_fail(self, sk):
        """连续几次服务端毫无反应 → 打一条诊断，把可能原因连现状一起列出来。

        ★ 顺带记「这只怪打不动」：同一个目标连着几次都没回音，多半是它已经
          刷没了 / 是个假实体，一直对着它发只会卡死在这里。记到 SKIP_FAIL_N
          次就把它冷藏 SKIP_FAIL_SEC 秒，自动换下一只（2026-10-20）。
        """
        self._noack_sk[sk] = self._noack_sk.get(sk, 0) + 1
        n = self._noack_sk[sk]
        eid = getattr(self, 'atk_target', 0) or 0
        if eid:
            c = self._tgt_fail.get(eid, 0) + 1
            self._tgt_fail[eid] = c
            if c >= SKIP_FAIL_N:
                self._tgt_fail[eid] = 0
                self._skip_t[eid] = time.time() + SKIP_FAIL_SEC
                o = self.ent.get(eid) or {}
                self.log('   [自动] %s 连着 %d 次打过去服务端没反应 —— '
                         '先跳过 %.0f 秒，换别的怪'
                         % (o.get('name') or ('0x%08x' % eid), c, SKIP_FAIL_SEC))
        if n not in (2, 5, 20):
            return
        nm = (skill_cfg(sk) or {}).get('name') or ('技能%d' % sk)
        why = []
        if self.mp is not None:
            why.append('蓝 %s/%s' % (self.mp, self.mp_max or self._mp_seen_max or '?'))
        _mpc = self._skill_mp_cost.get(sk, 0)
        if _mpc:
            why.append('这招约耗 %d 蓝' % _mpc)
        _hpc = self._skill_hp_cost.get(sk, 0)
        if _hpc:
            why.append('约耗 %d 血' % _hpc)
        _left = self.skill_cd.get(sk, 0.0) - time.time()
        if _left > 0:
            why.append('冷却还有 %.1fs' % _left)
        _pq = prereq_of(sk)
        if _pq:
            why.append('前置：%s（%s）' % (_pq[1],
                       '在线' if self._summon_online(_pq[0]) else '不在线'))
        why.append('已学' if sk in self.learned else '没学？')
        self.log('[!] 「%s」连续 %d 次服务端无回应 —— 现状：%s'
                 % (nm, n, ' / '.join(why)))

    # ---------------- ⑥ 实体详情查询 / 附近玩家订阅

    def _query_pending(self):
        """把服务端给过的实体 ID 分批用 0x47e 查详情（真客户端 count 0→1→7→13→25）"""
        if not self.ent_pend or time.time() - self._t_query < 0.06:
            return
        batch = []
        while self.ent_pend and len(batch) < 47:
            x = self.ent_pend.pop(0)
            if x in self.ent_queried:
                continue
            self.ent_queried.add(x)
            batch.append(x)
        self._t_query = time.time()
        if batch:
            p = (struct.pack('<II', 4 + len(batch) * 4, len(batch)) +
                 b''.join(struct.pack('<I', x) for x in batch))
            try:
                self.w.sendall(wframe(0x47E, p))
            except Exception:
                pass

    def _ident_retry(self):
        """给「只有坐标、没有名字」的实体补查身份（0x46E 单查 + 0x47E 批量）

        ★ 2026-10-20 实测（日志 22:29~22:32）：新刷出来的怪只发坐标广播
          （0x6D3/0x6D4），没有 0x6B9 身份包，于是界面上一排「未知」，
          而选目标时又分不清是怪还是一只别人的召唤兽 —— 结果锁在一个
          0.3 米外的「未知」上一直打，旁边真正的平原草羊反而没人打。
          补查拿到 MNID 之后名字/类型/血量上限全都有，选目标也就准了。
        每个实体最多查 3 轮、每轮间隔 8 秒，查过就不再纠缠。
        """
        if self.w is None or not self.in_world:
            return
        now = time.time()
        if now - self._ident_t < 3.0:
            return
        self._ident_t = now
        pend = []
        for eid, o in self.ent.items():
            if o.get('mnid') or o.get('name'):
                continue
            n = self._ident_try.get(eid, 0)
            if n >= 3:
                continue
            if now - self._ident_last.get(eid, 0.0) < 8.0:
                continue
            self._ident_try[eid] = n + 1
            self._ident_last[eid] = now
            pend.append(eid)
        if not pend:
            return
        try:
            for eid in pend[:12]:
                self.w.sendall(wframe(0x46E, struct.pack('<I', eid)))
            body = (struct.pack('<II', 4 + len(pend) * 4, len(pend)) +
                    b''.join(struct.pack('<I', x) for x in pend))
            self.w.sendall(wframe(0x47E, body))
            # 日志节流：连着补查时不刷屏（前 3 次 + 每 20 次）
            self._ident_n = getattr(self, '_ident_n', 0) + 1
            if self._ident_n <= 3 or self._ident_n % 20 == 0:
                self.log('   [身份] 补查 %d 个没名字的实体（第 %d 轮）'
                         % (len(pend), max(self._ident_try.values() or [0])))
        except Exception:
            pass

    def _sub_player(self, eid):
        """为附近玩家订阅数据（回 0x46c）"""
        if eid in self.rp_pl:
            return
        self.rp_pl.add(eid)
        try:
            self.w.sendall(wframe(0x46C, struct.pack('<I', eid)))
        except Exception:
            pass

    # ---------------- ③ 服务端自动战斗开关
    def do_bot(self, on):
        if not self.in_world or self.w is None:
            self.log('[!] 站桩打怪失败：当前不在世界中（请先进入游戏）')
            self.ev.put(('bot_res', {'ok': False, 'msg': '未进入世界'}))
            return
        if not self.scene['done']:
            self.log('[!] 站桩打怪：场景序列还没跑完（角色未激活），再等 1~2 秒')
            self.ev.put(('bot_res', {'ok': False, 'msg': '场景未就绪'}))
            return
        try:
            self.w.sendall(wframe(0x4C7, BOT_ON if on else BOT_OFF))
            self.bot_on = bool(on)
            self.bot_last = time.time()
            self.bot_stat_t = time.time()
            if on:
                px, py = (self.pos[0], self.pos[1]) if self.pos else (0.0, 0.0)
                self.log('   ★ 已发送 0x4c7 = 01 —— 服务端自动战斗【开启】')
                self.log('     活动中心 = 当前位置 (%.2f, %.2f)' % (px, py))
                self.log('     站桩别走远；打什么怪由服务端决定。换点流程：关 → 传送 → 再开')
            else:
                self.log('   ★ 已发送 0x4c7 = 00 —— 服务端自动战斗【关闭】')
            self.ev.put(('bot_res', {'ok': True, 'on': bool(on)}))
            self.st(bot=bool(on))
        except Exception as ex:
            self.log('[!] 自动战斗指令发送失败：%s' % ex)
            self.ev.put(('bot_res', {'ok': False, 'msg': str(ex)}))

    # ---------------- ★ 传送到位（0x407 · 2026-10-17 两次实测确认）
    def do_goto(self, x, y, z=0.0):
        """0x407 s_nCS_PlayerPosition —— 让角色直接到位（服务端采纳并持久化）。

        帧格式（必须精确 16 字节，短一字节服务端回 RST）：
            [u32 角色ID][f32 x][f32 y][f32 z]

        实测证据（两次全中）：
            发出 (4457.00, 4589.00) → 重登 0x603 @0x49 读出 (4457.00, 4589.00)
            发出 (4416.00, 4472.00) → 重登 0x603 @0x49 读出 (4416.00, 4472.00)

        注意：0x489 / 0x48b / 0x48a 是"客户端上报自己已经走到哪了"的通知帧，
        服务端只做 AOI 广播（0x6d3 / 0x6d4），不会执行位移 —— 不要用它们。
        """
        if not self.in_world or self.w is None:
            self.log('[!] 传送失败：当前不在世界中（请先进入游戏）')
            self.ev.put(('goto_res', {'ok': False, 'msg': '未进入世界'}))
            return
        cid = (self.picked_cid or 0) & 0xFFFFFFFF
        if not cid:
            cid = ((self.online_role or {}).get('cid') or 0) & 0xFFFFFFFF
        if not cid:
            self.log('[!] 传送失败：拿不到角色ID（请重新读取角色再进入）')
            self.ev.put(('goto_res', {'ok': False, 'msg': '无角色ID'}))
            return
        try:
            x, y, z = float(x), float(y), float(z)
        except (TypeError, ValueError):
            self.log('[!] 传送失败：坐标不是合法数字')
            self.ev.put(('goto_res', {'ok': False, 'msg': '坐标非法'}))
            return
        if not (0 < x < 20000 and 0 < y < 20000):
            self.log('[!] 传送失败：坐标超出合理范围（0 ~ 20000）')
            self.ev.put(('goto_res', {'ok': False, 'msg': '坐标越界'}))
            return
        # ★ z 千万别填 0：0x407 带 z=0 时服务端很可能直接忽略整条指令，
        #   而我们又乐观地把 self.pos 改成目标点 → 人还在原地，界面却以为到了，
        #   于是所有距离都差一个传送位移（"明明贴着怪却显示 30 多米" 就是这么来的）。
        #   这里三级兜底：界面填的 → 最近实体所在地面高度 → 自己上次的 z。
        if not z:
            nz = [o['z'] for o in self.ent.values() if o.get('z')]
            if nz:
                z = max(set(nz), key=nz.count)
            elif self.pos and self.pos[2]:
                z = self.pos[2]
        try:
            self.w.sendall(wframe(0x407, struct.pack('<Ifff', cid, x, y, z)))
            self.pos = (x, y, z)
            self.pos_set_t = time.time()
            # 标记"未确认"：等服务端用 0x62B 回写我们的坐标才算真到位
            self._pos_unconfirmed = time.time()
            self.log('   ★ 已发送传送指令 0x407：角色ID=%d → (%.2f, %.2f, %.2f)'
                     % (cid, x, y, z))
            self.log('     先按目标点算距离；3 秒内收不到服务端 0x62b 回执会提示')
            # ★ 传送后原来那批实体是旧位置的，服务端不会主动重推整张清单，
            #   必须清台账 + 重新做一次 AOI 握手，否则新位置的怪一个都看不到。
            self._need_aoi = time.time()
            self.ev.put(('goto_res', {'ok': True, 'pos': (x, y, z)}))
            self.st(pos=self.pos)
        except Exception as ex:
            self.log('[!] 传送发送失败：%s' % ex)
            self.ev.put(('goto_res', {'ok': False, 'msg': str(ex)}))

    def _dump_frame(self, cmd, pl):
        """把所有收到的包按行写到文件（排障用，默认关闭）"""
        try:
            if self._rxfile is None:
                self._rxfile = open(os.path.join(_APPDIR, '极光助手_收包.txt'),
                                    'w', encoding='utf-8')
                self.log('   [抓包] 开始记录收包 → 极光助手_收包.txt')
            self._rxfile.write('%.3f 0x%03X %4d %s\n'
                               % (time.time(), cmd, len(pl), pl[:400].hex()))
            self._rxfile.flush()
        except Exception:
            pass

    def _resync_scene(self, clear=False):
        """重新拉一次周围实体（0x47e AOI 握手 + 视野 + 空查）

        clear=True  → 清台账重来（传送/换点用：旧位置的实体全是过时的）
        clear=False → **轻刷新**：只重发视野 + 空查，台账留着。给「怪物实时刷新」用，
                      这样新刷出来的怪会被服务端补推过来，而已经记下的
                      血量/身份/坐标不丢。
                      ⚠ 轻刷新**故意不发** `0x47E [12,2,[1,自己]]` 那一发：
                        那是「我刚进 AOI」的首次申报，每隔 8 秒重发一次会把
                        服务端对「我已经知道哪些实体」的状态搅乱（2026-10-20
                        夜里怀疑它就与「新刷的怪一直没身份」有关），
                        只重发视野 + `0x47E [4,0]` 空查就够了。
        """
        if self.w is None:
            return
        cid = (self.picked_cid or 0) & 0xFFFFFFFF
        old = len(self.ent)
        if clear:
            self.ent.clear()
            self.ent_seen.clear()
            self.ent_pend = []
            self.ent_queried.clear()
            self._skip_t.clear()        # 整张名单重来，旧账也一并清掉
            self._tgt_fail.clear()
        try:
            if clear:
                # AOI 握手首查：[u32 4+N*4][u32 N][u32 元素×N]，元素 = [1, 自己]
                self.w.sendall(wframe(0x47E, struct.pack('<II', 12, 2) +
                                      struct.pack('<II', 1, cid)))
            # 视野（真客户端 0x425 载荷：地图ID + 一组视距参数）
            mid = (self.map_id or 0) & 0xFFFFFFFF
            self.w.sendall(wframe(0x425, struct.pack('<I', mid) +
                                  bytes.fromhex('001000004010000000120000c0120000')))
            for _ in range(3 if clear else 2):
                self.w.sendall(wframe(0x47E, struct.pack('<II', 4, 0)))
        except Exception as ex:
            self.log('[!] 重新拉取实体失败：%s' % ex)
            return
        if clear:
            self.log('   → 已重新请求周围实体（清掉旧台账 %d 个）' % old)
        else:
            # 轻刷新每 8 秒一次，别刷屏：第 1 次和之后每 10 次才念一句
            self._aoi_n += 1
            if self._aoi_n == 1 or self._aoi_n % 10 == 0:
                self.log('   [刷新] 第 %d 次重新申报视野（台账 %d 个）'
                         % (self._aoi_n, len(self.ent)))

    # ---------------- 主循环
    def run(self):
        while self.running:
            try:
                cmd, kw = self.cmds.get(timeout=0.05)
            except queue.Empty:
                if self.w is not None:
                    # ★★★ BUGFIX 2026-10-21：以前这里裸调 _recv_once()。
                    #   收包/解析里任何一次异常都会把 **整个后台线程打死**，
                    #   之后命令队列再也没人处理 —— 表现就是"点登录毫无反应、
                    #   一个都登不上"，而且界面还在正常刷新，根本看不出线程死了。
                    try:
                        self._recv_once()
                    except Exception as ex:
                        self.log('[!] 收包处理异常（已忽略，线程继续）：%s' % ex)
                # ★ 2026-10-21：自动凝神术的周期检查 —— 不能只靠属性包触发，
                #   没包进来（站着不动 / 射程内没怪）时也得看血蓝
                try:
                    self._heal_tick()
                except Exception:
                    pass
                continue
            try:
                if cmd == 'login':
                    # ★★★ 2026-10-21 去掉「失败 3 秒后自动再试一次」。
                    #   服务端对同一 IP 的连接频率有限制，失败后自动重试等于
                    #   自己往枪口上撞 —— 实测（12:45）连登录服都开始回
                    #   WinError 10054（远程主机强迫关闭）了，越自动重试越糟。
                    #   现在失败就是失败，由界面提示用户等几分钟再手动点。
                    self.do_login(kw['host'], kw['port'],
                                  kw['acct'], kw['pwd'])
                elif cmd == 'relogin':
                    self.do_login(self._host, self._port, self._acct, self._pwd,
                                  silent=True)
                elif cmd == 'loadroles':
                    self.do_load_roles(kw['line'])
                elif cmd == 'picklines':
                    self.do_pick_lines(kw.get('role'))
                elif cmd == 'unpick':
                    self.do_unpick()
                elif cmd == 'enter':
                    self.do_enter(kw['line'], kw.get('role_id'),
                                  kw.get('wline_i', 0), kw.get('char_idx'),
                                  kw.get('role_name'), kw.get('wline_name'))
                elif cmd == 'goto':
                    self.do_goto(kw['x'], kw.get('y'), kw.get('z', 0.0))
                elif cmd == 'bot':
                    self.do_bot(kw['on'])
                elif cmd == 'attack':
                    self.do_attack(eid=kw.get('eid', 0), skill=kw.get('skill', 0),
                                   group=kw.get('group', 0), step=kw.get('step', 0))
                elif cmd == 'use':
                    self.do_use_skill(skill=kw.get('skill', 0),
                                      group=kw.get('group', 0),
                                      step=kw.get('step', 0),
                                      eid=kw.get('eid', 0))
                elif cmd == 'sweep':
                    self.do_sweep()
                elif cmd == 'relive':
                    self.do_relive()
                elif cmd == 'radius':
                    try:
                        r = max(1.0, min(500.0, float(kw.get('r') or RADIUS)))
                    except Exception:
                        r = RADIUS
                    if abs(r - self.radius) > 0.01:
                        self.radius = r
                        self.log('   检测半径 = %.0f 米' % self.radius)
                elif cmd == 'dump':
                    self.dump_rx = bool(kw.get('on'))
                    if not self.dump_rx and self._rxfile is not None:
                        try:
                            self._rxfile.close()
                        except Exception:
                            pass
                        self._rxfile = None
                    self.log('   [抓包] %s' % ('开启' if self.dump_rx else '关闭'))
                elif cmd == 'show_npc':
                    self.show_npc = bool(kw.get('on'))
                    self.log('   列表%s显示 NPC' % ('' if self.show_npc else '不再'))
                elif cmd == 'refresh':
                    # 界面上的「刷新」按钮：立刻重拉一次周围实体（清台账重来）
                    self._resync_scene(clear=True)
                    self._nofind_t = 0.0
                elif cmd == 'blacklist':
                    # 界面上勾选的「不打这只怪」——按名字，刷新出来也不打
                    old = set(self.bl)
                    self.bl = set(str(x).strip() for x in (kw.get('names') or [])
                                  if str(x).strip())
                    save_blacklist(self.bl)
                    for nm in sorted(self.bl - old):
                        self.log('   × 已排除「%s」—— 以后刷新出来也不打' % nm)
                    for nm in sorted(old - self.bl):
                        self.log('   ○ 「%s」取消排除，恢复打它' % nm)
                elif cmd == 'probe':
                    self.do_probe(kw.get('kw') or '',
                                  kw.get('group'), kw.get('step'))
                elif cmd == 'auto':
                    self.set_auto_atk(kw['on'], kw.get('skill'),
                                      kw.get('group', 0), kw.get('step', 0),
                                      combo=kw.get('combo'))
                elif cmd == 'team':
                    self.set_auto_team(kw['on'])
                elif cmd == 'heal':
                    # ★ 2026-10-21：血/蓝低于阈值自动放凝神术
                    self.set_auto_heal(kw.get('on'), kw.get('pct'))
                elif cmd == 'bag':
                    self.do_bag_refresh()
                elif cmd == 'use_once':
                    self.use_item(kw['slot'], kw['iid'], kw.get('cont', 1))
                elif cmd == 'use_loop':
                    self.start_use_until_empty(kw['slot'], kw['iid'],
                                               kw.get('cont', 1))
                elif cmd == 'use_stop':
                    if self._use_loop:
                        self.log('   [物品] 已停止循环使用')
                    self._use_loop = None
                elif cmd == 'logout':
                    self.logout('用户下线')
                elif cmd == 'discard':
                    # ★ 2026-10-21 多线程录入：这条录入连接用完了，断开并结束线程。
                    #   界面已经把 PROBE['cur'] 指向新连接，不会再读它的队列。
                    self.logout('录入连接已回收')
                    self.running = False
                elif cmd == 'quit':
                    self.logout('退出程序')
                    self.running = False
            except Exception as ex:
                self.log('[!] 指令执行出错：%s' % ex)

    # ---------------- 关闭
    def close_world(self, mark=True):
        # ★ BUGFIX 2026-10-21：只有**真的关掉了一个连接**才记"断开时刻"。
        #   原来无条件记，可 do_login 里 _acct 已经换成新账号了，
        #   于是新账号的 World 冷却从"刚登录"开始算 —— 首次进世界白等 5 秒。
        _had = self.w is not None
        if self.w is not None:
            try:
                self.w.shutdown(socket.SHUT_RDWR)
            except Exception:
                pass
            try:
                self.w.close()
            except Exception:
                pass
        self.w = None
        self.in_world = False
        self.online_role = None
        self.pick_role = None
        self.pick_wline = None
        self.picked_cid = None
        self.wlines = []
        self.state = 'logged' if self.ls else 'idle'
        if mark and _had:
            self._t_world_closed = time.time()
            _ac = (getattr(self, '_acct', '') or '').strip()
            if _ac:
                _WORLD_CLOSE_BY_ACCT[_ac] = self._t_world_closed

    def drop_world(self, reason=''):
        """★ 只断 World，保留登录会话。
        换分区 / 换线都要走这里 —— 不能顺手把登录服连接也关了，
        否则用户看到的就是"切个分区就掉线、要重新登录"。"""
        was_in = self.in_world
        dur = (time.time() - self.t_inworld) if was_in else 0
        # ⚠ 这里**不能**调 release_pick：走到 drop_world 说明连接已经断了 / 被 RST，
        #   再往死 socket 上发 0x210 只会触发一次无谓的异常。
        self.close_world()
        self.ev.put(('offline', None))
        self.st(step='World 已断开（可重新选分区）', inworld=False,
                hb=0, nrecv=0, dur=0, role='')
        if reason:
            self.log('[*] %s' % reason)
            if dur:
                self.log('    本次在线 %.0f 秒，心跳 %d 次' % (dur, self.hb_count))

    def close_all(self):
        self.close_world()
        if self.ls is not None:
            try:
                self.ls.close()
            except Exception:
                pass
        self.ls = None
        # 完整下线 = 整条流程结束，角色/线路一并清掉，下次登录从干净状态开始
        self.roles = []
        self._roles_seen = set()
        self.roles_last_t = 0.0
        self.wlines = []
        self.cur_line = None
        self.state = 'idle'

    def do_unpick(self):
        """录完一个角色：退回角色选择界面，**保持 World 连接不断**。

        ★★★ 2026-10-21 关键结论：服务端对「同一账号的 World 连接」有冷却 ——
          一条 World 断掉后立刻再连，会被直接关闭（就是用户看到的
          「连接被服务端关闭（多半是该账号还挂在游戏客户端上）」），而且
          实测不是几秒能等到的事。协议里也**没有**"主动退出 World 会话"的包
          （只有 0x207 握手 / 0x205 选角 / 0x20f 进世界 / 0x210 退回角色选择）。
          所以正确做法是：录入时压根不要重连 —— 发 0x210 退回角色选择界面，
          连接留着，接着点下一个角色就能继续录（pick_and_fetch_lines 里
          已经带了 0x210 → 0x205 的序列，真客户端实测可用）。
        """
        try:
            if (self.w is not None and self.picked_cid is not None
                    and not self.in_world):
                self.w.sendall(wframe(0x210, b'\x24'))
                self.log('[3] 已退回角色选择界面（连接保持，可继续录下一个角色）')
                self.pump(0.5)
            self.picked_cid = None
            self.pick_role = None
            self.wlines = []
            self.ev.put(('wlines', []))
            self.ev.put(('unpicked', None))
        except Exception as ex:
            self.log('[!] 退回角色选择失败：%s' % ex)

    def release_pick(self, wait=0.7):
        """退回角色选择界面（0x210）—— 断开前必须做这一步。

        ★★★ 2026-10-21 用户实测：录入一个角色后马上录入第二个，连续报
          「连接被服务端关闭（多半是该账号还挂在游戏客户端上）」。
          根因就是我们**选了角色（0x205）就直接关 socket**，服务端那边这个角色
          还挂在"已选角"状态上，同账号再连一条 World 会被直接关掉。
          真客户端退出角色界面发的就是 0x210 载荷 0x24（见 pick_and_fetch_lines）。
          这里补上：只要选过角、又还没进世界，就先退回角色选择再断。
        注意：已经 in_world 的角色不能发这个包（那是另一个流程），只关 socket。
        """
        if self.w is None or self.picked_cid is None or self.in_world:
            return
        # ★ BUGFIX 2026-10-21：这里必须先清 picked_cid 再 pump。
        #   否则 pump → _recv_once 发现连接已断 → drop_world → 又调 release_pick
        #   → 条件仍然成立 → 再 pump …… 无限递归，最后 RecursionError 打死线程。
        if getattr(self, '_releasing', False):
            return
        self._releasing = True
        self.picked_cid = None
        try:
            self.w.sendall(wframe(0x210, b'\x24'))
            self.log('[3] 已退回角色选择界面（释放角色占用）')
            self.pump(wait)          # 让服务端把这几个包收完再断
        except Exception:
            pass
        finally:
            self._releasing = False

    def logout(self, reason=''):
        # ★ 先退角色、再断连接 —— 否则服务端会认为这个角色还占着，
        #   同账号马上重新登录会被拒（用户 10:57 报的就是这个）
        self.release_pick()
        self.abort = True               # 打断正在跑的阻塞流程
        dur = (time.time() - self.t_inworld) if self.in_world else 0
        self.close_all()
        self.ev.put(('offline', None))
        self.st(conn='已下线', step='已下线（可重新登录）',
                inworld=False, hb=0, nrecv=0, dur=0, role='')
        if reason:
            self.log('[*] %s —— 已断开连接，账号已释放' % reason)
            if dur:
                self.log('    本次在线 %.0f 秒，心跳 %d 次' % (dur, self.hb_count))


# ================================================================ 界面
def build_gui(boot):
    """★ 2026-10-21 多开版

    boot = 左侧「录入」专用的那条连接（读区服/分区/角色/线路，用完就断）。
    界面其余部分（传送、打怪、技能格、血蓝、怪物列表）一律走 client 代理，
    指向中间角色列表里**当前选中的那个角色**；它没上线时退回离线占位。
    """
    import tkinter as tk
    from tkinter import ttk, messagebox

    BG = '#F0F0F0'
    PANEL = '#FFFFFF'
    FG = '#1A1A1A'
    RED = '#B02020'
    MUT = '#8A8A8A'
    GRN = '#0F7B2E'
    WARN = '#B45309'
    F = lambda s, w='normal': ('微软雅黑', s, w)

    root = tk.Tk()
    root.title('极光世界 · 助手 %s' % APP_VER)
    root.geometry('1160x860')
    root.minsize(1120, 800)
    root.configure(bg=BG)

    st = ttk.Style()
    try:
        st.theme_use('vista')
    except Exception:
        try:
            st.theme_use('clam')
        except Exception:
            pass
    st.configure('.', font=F(9))
    st.configure('Treeview', font=F(9), rowheight=23,
                 background=PANEL, fieldbackground=PANEL, foreground=FG)
    st.configure('Treeview.Heading', font=F(9, 'bold'))
    st.configure('TCheckbutton', background=BG)
    # 主操作按钮（大、醒目）；次要按钮（换线/创建）
    st.configure('FB.TButton', font=F(10, 'bold'), padding=(12, 7))
    st.configure('MB.TButton', font=F(9), padding=(8, 5))

    # ======================================================== 多开会话基础设施
    #   ★ 2026-10-21 用户要求：中间角色列表里的角色要能**同时在线多个**。
    #     每个角色 = 一个独立 Client（独立 TCP/心跳/技能CD）+ 一份界面缓存，
    #     全部挂在 SESS 里；CUR['key'] 是「当前选中」的那个。
    #   界面里原来的 client.xxx 全部走下面的代理，自动指向选中角色的 Client，
    #   所以 60 处旧代码一行都不用改；选中一个没上线的角色时退回 _OFF。
    # ★★★ 2026-10-21 多线程录入（正式版）
    #   用户要求：录入部分改成多线程。做法是
    #     **每点一次「登录」= 一条全新 Client 线程 + 全新 socket + 全新事件队列**，
    #   旧的那条异步回收（discard = 断开 + 线程退出），不再复用同一个 Client 对象。
    #
    #   为什么以前不敢这么做（旧注释留在这里当教训）：
    #     当时是「每次登录丢掉旧连接、立刻开新连接」，没有任何节流，短时间内同一个
    #     IP 连续建/断 TCP，被服务端判成异常连接直接拒 —— 表现就是"一个都登不上"。
    #   现在能成立的关键是 Client._login_gate()：所有线程统一排队领号，
    #     相邻两次真正开始连接至少隔 1.2 秒，同账号再等 3 秒。
    #     所以这里是"并发 + 有序"：多条录入连接可以同时活着、各自读各自的分区，
    #     但"发起连接"这个动作是串行排队的，服务端看到的永远是平缓的建立节奏。
    #
    #   好处：
    #     ① 不同账号互不阻塞 —— A 在读角色时，B 可以直接点登录，不用等 A 走完；
    #     ② 不存在旧连接的 state/roles/token/socket 残留带进下一次；
    #     ③ 某条连接卡住或被 RST，不会连坐整条录入通道。
    #   pc 始终指向「当前这条录入连接」，所以下面所有 pc.xxx 一行都不用改。
    PROBE = {'cur': boot, 'all': [], 'n': 0}

    class _IdleCl(object):
        """没有活跃录入连接时的占位：属性齐全，pc.xxx 永远不会抛异常"""
        ev = queue.Queue()
        ls = None
        w = None
        roles = []
        lines = []
        areas = []
        wlines = []
        cur_line = None
        token = None
        _acct = ''
        is_probe = True
        abort = False
        running = False

        def post(self, *a, **k):
            return False

        def is_alive(self):
            return False

    _IDLE = _IdleCl()

    if boot is not None:
        boot.is_probe = True
        boot.tag = '录入'
        PROBE['all'].append(boot)

    class _ProbeProxy(object):
        def __getattr__(self, n):
            cl = PROBE.get('cur')
            if cl is not None and hasattr(cl, n):
                return getattr(cl, n)
            return getattr(_IDLE, n, None)

        def __setattr__(self, n, v):
            cl = PROBE.get('cur')
            if cl is not None:
                setattr(cl, n, v)

    pc = _ProbeProxy()

    def retire_probe(cl):
        """把一条用过的录入连接丢到后台回收。

        ★ 必须异步：不能等它断完再让用户点下一次登录，否则又回到"串行阻塞"。
          也不能直接 close socket —— 先 abort 打断它正在跑的 pump_until
          （读角色可能要等 20 秒），再由它自己的线程执行 discard。
        """
        if cl is None:
            return
        try:
            cl.abort = True
        except Exception:
            pass
        try:
            cl.post('discard')
        except Exception:
            pass

    def new_probe(acct=''):
        """★ 新建一条录入连接（独立线程 / 独立 socket / 独立队列），旧的自动回收。

        acct 只用来给日志打前缀（tag），多开录入时能分清哪条连接在说话。
        """
        old = PROBE.get('cur')
        _ac = (acct or '').strip()
        # ★★★ 2026-10-21 换账号必须先放掉**别的账号**的连接。
        #   实测：PARK 里留着 gk623513 的连接时，gk623520 的 World 握手直接被
        #   flag=1 拒掉，还把 gk623513 那条顶成 RST。服务端对同 IP 的连接名额很紧。
        for o in list(PARK):
            if (getattr(o, '_acct', '') or '').strip() == _ac:
                continue                     # 同账号留着，等会儿复用
            try:
                PARK.remove(o)
            except ValueError:
                pass
            retire_probe(o)
        PROBE['n'] += 1
        ev = queue.Queue()
        cl = Client(ev)
        cl.is_probe = True
        cl.tag = ('录入:%s' % acct) if acct else ('录入%d' % PROBE['n'])
        cl.start()
        PROBE['cur'] = cl
        PROBE['all'].append(cl)
        if old is not None and old is not cl:
            retire_probe(old)
        return cl

    def probe_gc():
        """回收已退出的录入线程，避免线程和队列越攒越多"""
        cur = PROBE.get('cur')
        keep = []
        for c in PROBE['all']:
            if c is cur or c.is_alive():
                keep.append(c)
        PROBE['all'] = keep

    # ============================================================ 录入连接闲置池
    # ★★★ 2026-10-21 实测踩坑（12:40 探针）：
    #   服务端对**同一账号的 World 会话**释放极慢 —— 断开后 25 秒内重连，
    #   服务端连 0x20C 都不回（只回个 0x3001 hello），15 秒后超时；
    #   而同一时刻换别的账号是秒连的。也就是说：卡的从来不是"并发连接数"，
    #   是**同一个账号不许快速重连**。
    #   老版本 v3.0 之所以"登录都正常"，就是因为它录完**不断连接**，
    #   同账号接着录下一个角色时压根不重连（do_unpick 只发 0x210 退回角色选择）。
    #   所以这里不能"录完就断"，要**把连接留着下次复用**：
    #     · 多个账号的连接可以同时挂着（多线程录入的意义还在，互不阻塞）
    #     · 同一账号下次录入直接拿回自己那条，不产生任何新连接 → 不撞冷却
    PARK = []                         # 闲置的录入连接（已登录、World 还连着）
    PARK_MAX = 1                      # ★ 2026-10-21 改回 1：服务端对同 IP 的连接
                                      #   名额很紧，池子里多留一条就会把后面账号的
                                      #   握手挤成 flag=1（实测 12:41:25）

    def park_probe(cl):
        """把用完的录入连接收进闲置池（**不断开**），供同账号下次复用"""
        if cl is None:
            return
        try:
            if not cl.is_alive():
                return
        except Exception:
            return
        _ac = (getattr(cl, '_acct', '') or '').strip()
        # 同账号只留最新的一条，旧的直接回收
        for i, o in enumerate(PARK):
            if (getattr(o, '_acct', '') or '').strip() == _ac:
                old = PARK[i]
                PARK[i] = cl
                if old is not cl:
                    retire_probe(old)
                return
        PARK.append(cl)
        while len(PARK) > PARK_MAX:
            retire_probe(PARK.pop(0))

    def unpark_probe(acct):
        """从这个账号的闲置池里取一条还能用的连接（没有就 None）"""
        _ac = (acct or '').strip()
        if not _ac:
            return None
        for i, o in enumerate(list(PARK)):
            if (getattr(o, '_acct', '') or '').strip() != _ac:
                continue
            try:
                alive = o.is_alive()
            except Exception:
                alive = False
            # ls（登录服会话）还在才算能复用；只剩 World 没用，登录服断了就没 token
            if alive and (o.ls is not None or o.w is not None):
                PARK.pop(i)
                return o
            PARK.pop(i)
            retire_probe(o)
        return None

    SESS = {}                         # key -> 会话 dict
    CUR = {'key': None}
    ARCH = load_arch()                # 角色档案（录入的结果）

    CLS_NAME = {0: '剑系', 1000: '通用', 2000: '通用', 5000: '法术系',
                6000: '道系', 7000: '巫士', 8000: '灭魔咒'}

    def cls_of(s):
        """从该角色已学技能的段分布推断职业（服务端不下发职业名）"""
        ids = [x for x in (s.get('learned') or ()) if x]
        if not ids:
            return '—'
        cnt = {}
        for x in ids:
            seg = skill_block(x)
            if seg in (1000, 2000):
                continue           # 1000/2000 段是通用技（攻击/凝神…），不代表职业
            cnt[seg] = cnt.get(seg, 0) + 1
        if not cnt:
            return '通用'
        seg = max(cnt, key=lambda k: (cnt[k], -k))
        return CLS_NAME.get(seg, '%d 段' % seg)

    class _Offline(object):
        """没选中角色 / 选中但没上线时的占位：属性齐全，界面不会因为取属性崩"""
        in_world = False
        ls = None
        w = None
        learned = set()
        learned_cid = 0
        skill_cd = {}
        grp_cd = 0.0
        pos = None
        atk_sent = atk_ack = atk_hit = 0
        wlines = []
        roles = []
        areas = []
        lines = []
        cur_line = None
        picked_cid = None
        online_role = None
        _busy_id = None
        t_inworld = 0.0
        abort = False
        ev = queue.Queue()

        def post(self, *a, **k):
            return False

        def _empty_hint(self):
            return '该角色未上线'

    _OFF = _Offline()

    class _CurProxy(object):
        """当前选中角色的 Client 代理（没上线就用离线占位）"""

        def _cl(self):
            s = SESS.get(CUR['key']) or {}
            return s.get('cl')

        def __getattr__(self, n):
            cl = self._cl()
            if cl is not None:
                return getattr(cl, n)
            return getattr(_OFF, n)

        def __setattr__(self, n, v):
            cl = self._cl()
            if cl is not None:
                setattr(cl, n, v)

    client = _CurProxy()

    def sess():
        """当前选中的会话 dict（没选 → {}）"""
        return SESS.get(CUR['key']) or {}

    def new_session(row, cl=None):
        """给一个档案建会话（Client + 队列），不上线。

        cl 传了就用它（把「录入连接」直接接管成这个角色的会话连接，
        零重连 —— 见 online_one 里的说明）；不传就新建一条。
        """
        key = row['key']
        if cl is None:
            ev = queue.Queue()
            cl = Client(ev)
            cl.start()
        else:
            ev = cl.ev              # 必须用它自己的队列，_drain_session 从这里读
        cl.tag = row.get('name') or ''
        s = {'key': key, 'arch': row, 'cl': cl, 'ev': ev,
             'state': 'offline', 'msg': '', 'hp': None, 'hpmax': None,
             'mp': None, 'mpmax': None, 'dead': False,
             'learned': set(), 'npcs': [], 'auto': False, 'pos': None,
             'team': False, 'mates': [],
             'lv': None, 'exp': None, 'need': None,
             'wline': '', 'login_t': 0.0}
        SESS[key] = s
        return s

    def kill_session(key, reason=''):
        s = SESS.get(key)
        if not s:
            return
        cl = s.get('cl')
        if cl is not None:
            try:
                cl.post('quit')
            except Exception:
                pass
        s['state'] = 'offline'

    # ---------------------------------------------------------- 主区（三栏）
    def widen_popdown(cb, cols=26):
        """把下拉弹出的列表拉宽。
        不然「暮雪千山(今日新服)」这种长名字会被输入框的宽度截断，
        看起来就像"分区没加载全"。"""
        try:
            pd = cb.tk.call('ttk::combobox::PopdownWindow', cb)
            cb.tk.call(pd + '.f.l', 'configure', '-width', cols)
        except Exception:
            pass
        return cb

    main = tk.Frame(root, bg=BG)
    main.pack(fill='both', expand=True, padx=8, pady=(8, 4))
    main.columnconfigure(0, weight=0, minsize=268)
    main.columnconfigure(1, weight=1)
    main.columnconfigure(2, weight=0, minsize=318)
    main.rowconfigure(0, weight=1)

    col0 = tk.Frame(main, bg=BG, width=268)
    col0.grid(row=0, column=0, sticky='ns')
    col0.grid_propagate(False)
    col1 = tk.Frame(main, bg=BG)
    col1.grid(row=0, column=1, sticky='nsew', padx=10)
    col2 = tk.Frame(main, bg=BG, width=318)
    col2.grid(row=0, column=2, sticky='ns')
    col2.grid_propagate(False)

    # ---------------- 左栏：账号
    f_acc = tk.Frame(col0, bg=BG)
    f_acc.pack(fill='x')
    f_acc.columnconfigure(1, weight=1)
    tk.Label(f_acc, text='账号', bg=BG, fg=FG, font=F(10)).grid(
        row=0, column=0, sticky='w', pady=4)
    e_acct = tk.Entry(f_acc, font=F(11), width=13)
    e_acct.grid(row=0, column=1, sticky='we', ipady=3, pady=4, padx=(8, 0))
    tk.Label(f_acc, text='密码', bg=BG, fg=FG, font=F(10)).grid(
        row=1, column=0, sticky='w', pady=4)
    e_pwd = tk.Entry(f_acc, font=F(11), width=13, show='*')
    e_pwd.grid(row=1, column=1, sticky='we', ipady=3, pady=4, padx=(8, 0))
    btn_login = ttk.Button(f_acc, text='登  录', style='FB.TButton')
    btn_login.grid(row=2, column=1, sticky='we', pady=(10, 0), padx=(8, 0))

    tk.Frame(col0, bg='#C4C4C4', height=1).pack(fill='x', pady=8)

    # ---------------- 左栏：大区信息 / 分区
    f_sel = tk.Frame(col0, bg=BG)
    f_sel.pack(fill='x')
    f_sel.columnconfigure(1, weight=1)
    tk.Label(f_sel, text='大区信息', bg=BG, fg=FG, font=F(10)).grid(
        row=0, column=0, sticky='w', pady=5)
    cb_area = ttk.Combobox(f_sel, state='readonly', width=13, font=F(10))
    widen_popdown(cb_area, 18)
    cb_area.grid(row=0, column=1, sticky='we', pady=5, padx=(8, 0))
    tk.Label(f_sel, text='分区', bg=BG, fg=FG, font=F(10)).grid(
        row=1, column=0, sticky='w', pady=5)
    cb_zone = ttk.Combobox(f_sel, state='readonly', width=13, font=F(10))
    widen_popdown(cb_zone, 26)
    cb_zone.grid(row=1, column=1, sticky='we', pady=5, padx=(8, 0))

    tk.Frame(col0, bg='#C4C4C4', height=1).pack(fill='x', pady=8)

    # ---------------- 左栏：角色信息（4 个槽位）+ 线路 → 录入
    #   2026-10-21：原来的「进入游戏」改成「录 入」—— 把这里选好的
    #   账号/区服/分区/角色/线路 存成一条档案，进中间的角色列表。
    lf_slots = tk.LabelFrame(col0, text=' 读到角色点一下就填进下面 ',
                             bg=BG, fg=FG, font=F(10, 'bold'), bd=1,
                             relief='groove')
    lf_slots.pack(fill='x')
    slots = []
    for i in range(1, 5):
        fr = tk.Frame(lf_slots, bg=BG)
        fr.pack(fill='x', pady=2, padx=4)
        lb_no = tk.Label(fr, text=str(i), bg=BG, fg=FG, font=F(10), width=2)
        lb_no.pack(side='left')
        lb_nm = tk.Label(fr, text='空', bg=BG, fg=MUT, font=F(10),
                         anchor='w', width=8)
        lb_nm.pack(side='left', fill='x', expand=True)
        # 圆润边框，跟其它按钮统一（ttk vista 主题自带圆角）
        bt = ttk.Button(fr, text='创建', width=6, style='MB.TButton')
        bt.pack(side='right')
        slots.append({'no': lb_no, 'name': lb_nm, 'btn': bt, 'role': None,
                      'row': fr, 'sel': False})

    # ★★★ 2026-10-21：角色名可以**手填**，不一定要连分区服务器读。
    #   实测服务端对同 IP 的 World 连接释放极慢，连续录入不同账号时几乎必被拒
    #   （握手后只回 2 帧、40 多秒后 RST）。所以录入默认**不连 World**，
    #   角色名自己填；想核对就点「读角色」临时读一次（可选）。
    f_rn = tk.Frame(col0, bg=BG)
    f_rn.pack(fill='x', pady=(8, 0))
    f_rn.columnconfigure(1, weight=1)
    tk.Label(f_rn, text='角色名', bg=BG, fg=FG, font=F(10)).grid(
        row=0, column=0, sticky='w', pady=4)
    e_role = tk.Entry(f_rn, font=F(10), width=9)
    e_role.grid(row=0, column=1, sticky='we', pady=4, padx=(8, 4))
    btn_role = ttk.Button(f_rn, text='读角色', width=6, style='MB.TButton')
    btn_role.grid(row=0, column=2, pady=4)

    # 线路（大世界线路）：原来在右栏「任务设置」里，右栏重做后搬到这里
    f_ln = tk.Frame(col0, bg=BG)
    # ★ 2026-10-21：这一行**不显示**了（左栏多了一行角色名，再放线路会把
    #   底部日志框挤出窗口）。控件本身留着，代码里 cb_line.get() 照样能用；
    #   想指定线路，在中间列表右键「编辑」里填。
    # f_ln.pack(fill='x', pady=(8, 0))
    f_ln.columnconfigure(1, weight=1)
    tk.Label(f_ln, text='线路', bg=BG, fg=FG, font=F(10)).grid(
        row=0, column=0, sticky='w', pady=4)
    # 线路不再读（读线路要选角，会把角色占住）；留空 = 上线时自动用第 1 条
    cb_line = ttk.Combobox(f_ln, state='normal', width=13, font=F(10),
                           values=[])
    cb_line.set('')            # 可留空；也能手打线路名（上线时按名字匹配）
    widen_popdown(cb_line, 20)
    cb_line.grid(row=0, column=1, sticky='we', pady=4, padx=(8, 0))

    btn_enter = ttk.Button(col0, text='录  入', style='FB.TButton')
    btn_enter.pack(fill='x', pady=(12, 0))

    # ---------------- 中栏：角色列表（录入的档案）
    #   2026-10-21：这里不再是"当前登录读到的 4 个角色"，而是**录入过的
    #   所有角色档案**，可以来自不同账号/区服 —— 点一条看数据，右侧点上线。
    # ★ 2026-10-21 用户要求：别用大红字，改成跟下面「打怪」一样的框式标题；
    #   列表本身吃满中栏剩余高度（角色多了也不用滚来滚去）。
    lf_roles = tk.LabelFrame(col1, text=' 角色列表 ', bg=BG, fg=FG,
                             font=F(10, 'bold'), bd=1, relief='groove')
    lf_roles.pack(fill='both', expand=True, pady=(2, 0))
    f_tv = tk.Frame(lf_roles, bg=PANEL, bd=1, relief='solid')
    f_tv.pack(fill='both', expand=True, padx=6, pady=(4, 6))
    cols = (('name', '角色', 100, 'w'), ('acct', '账号', 96, 'w'),
            ('zone', '分区', 146, 'w'), ('cls', '职业', 66, 'center'),
            ('stt', '状态', 88, 'center'))
    tv = ttk.Treeview(f_tv, columns=[c[0] for c in cols], show='headings',
                      height=5, selectmode='browse')
    for k, t, w, a in cols:
        tv.heading(k, text=t)
        tv.column(k, width=w, anchor=a, stretch=(k == 'zone'))
    sbv = ttk.Scrollbar(f_tv, orient='vertical', command=tv.yview)
    tv.configure(yscrollcommand=sbv.set)
    tv.pack(side='left', fill='both', expand=True)
    sbv.pack(side='right', fill='y')

    # ---------------- 中栏：打怪（2026-10-20 新版：技能格子）
    #   用户手绘框架：角色列表不变；怪物列表把「筛选范围/含NPC/记收包」
    #   提到标题行；下面技能区大改成 6 个攻击格 + 「开始」+ 2 个通用格。
    lf_fight = tk.LabelFrame(col1, text=' 打怪 ', bg=BG, fg=FG,
                             font=F(10, 'bold'), bd=1, relief='groove')
    lf_fight.pack(fill='x', pady=(10, 0))

    # —— 怪物列表标题行：筛选范围 / 含NPC / 记收包（从按钮行移上来）
    g_nh = tk.Frame(lf_fight, bg=BG)
    g_nh.pack(fill='x', padx=8, pady=(8, 2))
    tk.Label(g_nh, text='怪物列表', bg=BG, fg=FG,
             font=F(10, 'bold')).pack(side='left')
    tk.Label(g_nh, text='筛选范围', bg=BG, fg=MUT,
             font=F(9)).pack(side='left', padx=(14, 0))
    e_rng = tk.Entry(g_nh, font=F(10), width=4)
    e_rng.insert(0, str(int(RADIUS)))
    e_rng.pack(side='left', padx=(3, 0), ipady=1)
    tk.Label(g_nh, text='m', bg=BG, fg=MUT, font=F(9)).pack(side='left')
    show_npc_var = tk.BooleanVar(value=False)
    cb_npc = ttk.Checkbutton(g_nh, text='含NPC', variable=show_npc_var)
    cb_npc.pack(side='left', padx=(12, 0))
    dump_var = tk.BooleanVar(value=False)
    cb_dump = ttk.Checkbutton(g_nh, text='记收包', variable=dump_var)
    cb_dump.pack(side='left', padx=(6, 0))
    # ★ 「刷新」按钮：觉得列表旧了就点一下，立刻重拉周围实体（自动的每 8 秒一次）
    btn_ref = ttk.Button(g_nh, text='刷新', width=5)
    btn_ref.pack(side='left', padx=(12, 0))

    f_npc = tk.Frame(lf_fight, bg=PANEL, bd=1, relief='solid')
    f_npc.pack(fill='x', padx=8, pady=(2, 0))
    # ★ 2026-10-20 用户要求：怪名旁加个小方框，点一下出 ✗ = 排除这只怪，
    #   刷新出来也不打。为了给这一列腾地方，后面几列各缩了一点（总宽基本不变）。
    # ⚠ ID 列原来给 70 会截断（0x02625c80 要 ~78px，截图里只剩 0x0263b76），
    #   现在 82；名字列相应收窄一点，总宽 464 仍在框内。
    ncols = (('ex', '排除', 34, 'center'), ('name', '怪物', 104, 'w'),
             ('kind', '类型', 44, 'center'), ('lvl', '等级', 44, 'center'),
             ('dist', '距离', 56, 'center'), ('hp', '血量', 76, 'center'),
             ('eid', 'ID', 84, 'center'))
    tv_npc = ttk.Treeview(f_npc, columns=[c[0] for c in ncols],
                          show='headings', height=5, selectmode='browse')
    for k, t, w, a in ncols:
        tv_npc.heading(k, text=t)
        tv_npc.column(k, width=w, anchor=a, stretch=(k == 'name'))
    sb_npc = ttk.Scrollbar(f_npc, orient='vertical', command=tv_npc.yview)
    tv_npc.configure(yscrollcommand=sb_npc.set)
    tv_npc.pack(side='left', fill='both', expand=True)
    sb_npc.pack(side='right', fill='y')

    # —— 技能格子：6 攻击格 + 开始 + 2 通用格 ----
    #   空框点击 = 添加（弹已学技能列表）；填好固定在该格（存 技能格子.json）；
    #   攻击格可**多选**，点「开始」按格子顺序轮流放，冷却中的自动跳过；
    #   通用格点一下 = 手动放一次（不自动循环）；右键 = 清空/更换；
    #   冷却中图标变黑白 + 角上剩余秒数；图标放 技能图标/<ID>.png 自动生效。
    # ★★ 一排要放 6 攻击格 + 开始 + 2 通用格（可用宽 ~524px），
    #   格子缩到 52x50 + 间距 4（实测 54/5 会把最后一个通用格挤成 36px）
    SLOT_W, SLOT_H = 52, 50
    _atk0, _buf0 = load_slots()
    slot_sel = set()                    # 被选中的攻击格下标集合（可多选）
    # ★★★ 2026-10-21 修（用户反馈：「选中技能出绿框，点上方另一个角色，绿框消失」）：
    #   绿框原本是**全局一份**，load_slots_for() 里无条件 slot_sel.clear()，
    #   所以一切换角色就清空、切回来也不恢复 —— 看起来像「配置丢了」。
    #   绿框代表的是「这个**位置**参与连招」，属于角色自己的配置，
    #   必须跟 技能格子.json 里的绑定一样**按角色记住**。
    #   sel_memo：角色键 -> 该角色选中的格下标；last_slot_key：上一次装的是谁。
    sel_memo = {}
    last_slot_key = {'v': None}
    slots_atk, slots_buf = [], []
    _fit_cache = {}                      # (sid, 灰?) -> 缩到格子大小的图标
    _cell_cache = {}                     # (sid, 灰?, 选中?) -> (整格图, 有没有图标)

    # —— 格子悬停提示条：图标占满格子后没有汉字了，名字只能靠悬停看
    _tip = {'win': None}

    def _slot_tip_hide():
        w0 = _tip.get('win')
        if w0 is not None:
            try:
                w0.destroy()
            except Exception:
                pass
        _tip['win'] = None

    def _slot_tip_show(kind, idx):
        _slot_tip_hide()
        if _drag['kind'] is not None:
            return                       # 正在拖动，别弹名字条挡手
        try:
            w = (slots_atk if kind == 'atk' else slots_buf)[idx]
        except Exception:
            return
        sid = w['sid']
        if not sid:
            return
        cfg = skill_cfg(sid) or {}
        nm = (cfg.get('name') or '').strip() or ('技能%d' % sid)
        try:
            t = tk.Toplevel(root)
            t.wm_overrideredirect(True)
            tk.Label(t, text='%s   ID %d' % (nm, sid), bg='#404040',
                     fg='#FFFFFF', font=F(8), padx=4, pady=1).pack()
            t.update_idletasks()
            t.wm_geometry('+%d+%d' % (w['frame'].winfo_rootx(),
                                      w['frame'].winfo_rooty() + SLOT_H + 2))
            _tip['win'] = t
        except Exception:
            _tip['win'] = None

    g_lab = tk.Frame(lf_fight, bg=BG)
    g_lab.pack(fill='x', padx=6, pady=(8, 0))
    tk.Label(g_lab, text='技能-职业识别', bg=BG, fg=FG,
             font=F(10, 'bold')).pack(side='left')
    tk.Label(g_lab, text='空框=添加 · 可多选 · 拖动换位 · 右键=清空/更换',
             bg=BG, fg=MUT, font=F(8)).pack(side='left', padx=(6, 0))
    # ★ 2026-10-20 用户要求：去掉「（自动释放）」—— 通用格改纯手动，
    #   点一下放一次，不要一直释放。
    tk.Label(g_lab, text='点一下=放一次', bg=BG, fg=MUT,
             font=F(8)).pack(side='right')
    tk.Label(g_lab, text='通用技能', bg=BG, fg=FG,
             font=F(10, 'bold')).pack(side='right')

    # ★★ 用户要求（2026-10-20）：技能全部放一排：6 攻击格 + 开始 + 2 通用格，
    #   放不下就缩小格子（SLOT_W 80→54、SLOT_H 56→50）。
    g_slot = tk.Frame(lf_fight, bg=BG)
    g_slot.pack(fill='x', padx=6, pady=(4, 2))

    def _slot_fit(sid, gray):
        """图标缩到格子大小（64×64 → 52×50），灰度版单独缓存"""
        key = (int(sid), bool(gray))
        if key in _fit_cache:
            return _fit_cache[key]
        img = None
        ip = _icon_path(sid) if sid else None
        if ip:
            try:
                img = _icon_fit(tk.PhotoImage(file=ip), SLOT_W, SLOT_H, gray)
            except Exception:
                img = None
        _fit_cache[key] = img
        return img

    def _slot_photo(sid, gray, sel):
        """整格合成图：图标铺满 + 边框（选中 = 绿框），返回 (图, 有没有图标)

        ★★ 边框颜色取自 技能图标/选中边框源.png（用户给的绿框素材），
          见模块级的 _RING_SEL。选中框画在像素里而不是套一个 Frame，
          这样选中/未选中切换时图标**不会跳位置**，也不会因为 Tk 不做
          alpha 合成而露底色。
        """
        key = (int(sid), bool(gray), bool(sel))
        v = _cell_cache.get(key)
        if v is None:
            fit = _slot_fit(sid, gray) if sid else None
            v = (_cell_photo(fit, SLOT_W, SLOT_H, sel, PANEL), fit is not None)
            _cell_cache[key] = v
        return v

    # —— 技能格拖动换位：按住左键左右拖，拖到谁头上就跟谁交换（松手才落盘）
    _drag = {'kind': None, 'idx': None, 'cur': None, 'x0': 0, 'moved': False}

    def _slot_at_x(kind, x_root):
        """横坐标落在第几个格子上（按各格中心点最近的那个算）"""
        lst = slots_atk if kind == 'atk' else slots_buf
        best, bd = None, None
        for w in lst:
            fr = w['frame']
            try:
                c = fr.winfo_rootx() + fr.winfo_width() // 2
            except Exception:
                continue
            d = abs(x_root - c)
            if bd is None or d < bd:
                bd, best = d, w['idx']
        return best

    def _slot_swap(kind, i, j):
        """交换两个格子里的技能（空格子也会被换过去 = 自由挪位）

        ★★ 2026-10-21 修正：选中（绿框）跟**格子位置**走，不跟技能走。
           以前写的是「选中跟技能走」，结果用户把后面一个没选中的技能拖到
           第一格时，绿框跟着技能跑到后面去了 —— 连招里换进去的还是原来那
           几个，被拖上来的技能压根没进序列，看起来就是「界面动了、底层没
           动，还是按以前第一个加上去的技能放」。
           绿框的语义本来就是「这个**位置**参与连招，从左到右轮流放」，
           所以拖动只换技能，绿框留在原地不动。
        """
        lst = slots_atk if kind == 'atk' else slots_buf
        if i is None or j is None or i == j:
            return
        a, b = lst[i], lst[j]
        a['sid'], b['sid'] = b['sid'], a['sid']
        _slot_paint_all()

    def _slot_press(kind, idx, ev=None):
        _slot_tip_hide()
        _drag.update(kind=kind, idx=idx, cur=idx, moved=False,
                     x0=(ev.x_root if ev is not None else root.winfo_pointerx()))

    def _slot_drag(kind, idx, ev=None):
        if _drag['kind'] != kind or _drag['cur'] is None:
            return
        x = ev.x_root if ev is not None else root.winfo_pointerx()
        if not _drag['moved'] and abs(x - _drag['x0']) < 6:
            return                       # 手抖几像素不算拖，仍然当点击
        j = _slot_at_x(kind, x)
        if j is None or j == _drag['cur']:
            return
        _drag['moved'] = True
        _slot_swap(kind, _drag['cur'], j)
        _drag['cur'] = j

    def _combo_text():
        """当前连招顺序的人话文本（按格子从左到右），日志和提示条共用

        ★ 用户抱怨过「拖了以后不知道到底按什么顺序放」，所以每次换完位
          都把顺序念一遍 —— 日志里能查，界面提示条上也看得见。
        """
        _cb = _sel_combo()
        if not _cb:
            return '（没有选中任何技能）'
        return ' → '.join('%s(%d)' % ((skill_cfg(c[0]) or {}).get('name') or '?',
                                      c[0]) for c in _cb)

    def _slot_release(kind, idx, ev=None):
        moved, cur = _drag['moved'], _drag['cur']
        _drag.update(kind=None, idx=None, cur=None, moved=False)
        if not moved:
            _slot_click(kind, idx)       # 没拖动 → 就是普通点击
            return
        _slot_store()                    # 松手才写盘，拖的过程不落盘
        log('   技能格换位：%s #%d → #%d（左键按住可继续拖）'
            % ('攻击' if kind == 'atk' else '通用', idx + 1, (cur or idx) + 1))
        if kind == 'atk':
            log('   当前连招顺序（按格子从左到右）：%s' % _combo_text())
            if auto_state['on']:
                _sync_auto()             # 打怪途中换位 → 新顺序立刻生效
            elif slot_sel:
                lb_atk.configure(
                    text='已选中 %d 个技能，点「开始」按顺序轮流打' % len(slot_sel),
                    fg=FG)

    def _slot_make(parent, kind, idx, sid0):
        # ★ 不用 Frame 的 relief 做边框：图标要铺满整格，边框画在像素里（见 _cell_photo）
        fr = tk.Frame(parent, bg=PANEL, bd=0, highlightthickness=0,
                      width=SLOT_W, height=SLOT_H, cursor='hand2')
        fr.pack_propagate(False)
        fr.pack(side='left', padx=(0, 4))
        lb_i = tk.Label(fr, bg=PANEL, bd=0, anchor='center', compound='center',
                        font=F(7), justify='center', wraplength=SLOT_W - 4,
                        cursor='hand2')
        lb_i.pack(side='top', fill='both', expand=True)
        # 冷却秒数：右下角黑底白字小角标（图标铺满后必须自带底色，
        # 否则角标会是一块面板色）。**没冷却时用 place_forget 藏起来** ——
        # 空 Label 也会画自己的底色，一直挂着就是每格一个黑点。
        lb_c = tk.Label(fr, bg='#101010', fg='#FFFFFF', font=F(7), bd=0)
        w = {'frame': fr, 'icon': lb_i, 'cd': lb_c, 'cd_on': False,
             'sid': int(sid0 or 0), 'kind': kind, 'idx': idx, 'sel': False}
        for _c in (fr, lb_i):
            _c.bind('<Button-1>', lambda e, k=kind, i=idx: _slot_press(k, i, e))
            _c.bind('<B1-Motion>', lambda e, k=kind, i=idx: _slot_drag(k, i, e))
            _c.bind('<ButtonRelease-1>', lambda e, k=kind, i=idx:
                    _slot_release(k, i, e))
            _c.bind('<Button-3>', lambda e, k=kind, i=idx: _slot_menu(k, i))
            # 有图标时格子里没有汉字了 → 悬停显示「技能名 + ID」
            _c.bind('<Enter>', lambda e, k=kind, i=idx: _slot_tip_show(k, i))
            _c.bind('<Leave>', lambda e: _slot_tip_hide())
        return w

    # ★★ 一排布局：6 攻击格 + 开始 + 2 通用格（按手绘框架）
    for i, sid in enumerate(_atk0):
        slots_atk.append(_slot_make(g_slot, 'atk', i, sid))
    btn_go = ttk.Button(g_slot, text='开始', width=3, style='FB.TButton')
    btn_go.pack(side='left', padx=(2, 4))
    for i, sid in enumerate(_buf0):
        slots_buf.append(_slot_make(g_slot, 'buf', i, sid))

    # —— 复活 / 状态（「打它」2026-10-20 按用户要求移除）
    g_btn = tk.Frame(lf_fight, bg=BG)
    g_btn.pack(fill='x', padx=6, pady=(6, 2))
    btn_relive = ttk.Button(g_btn, text='复活', width=5)
    btn_relive.pack(side='left')
    # ★ 2026-10-21 新增：自动同意组队（收到邀请/入队申请就自动点「同意」）
    var_team = tk.BooleanVar(value=False)
    ck_team = ttk.Checkbutton(g_btn, text='自动同意组队/召唤', variable=var_team)
    ck_team.pack(side='left', padx=(10, 0))
    # ★ 2026-10-21 新增（用户要求）：血**或**蓝低于所选百分比 → 自动放凝神术
    #   百分比由玩家在后面的下拉里选（10%~90%），跟「自动同意组队」同一行。
    var_heal = tk.BooleanVar(value=False)
    ck_heal = ttk.Checkbutton(g_btn, text='血/蓝低于', variable=var_heal)
    ck_heal.pack(side='left', padx=(12, 0))
    var_heal_pct = tk.StringVar(value='30%')
    cb_heal = ttk.Combobox(g_btn, textvariable=var_heal_pct, width=4,
                           state='readonly',
                           values=['%d%%' % _v for _v in range(10, 91, 5)])
    cb_heal.pack(side='left', padx=(3, 0))
    lb_heal = tk.Label(g_btn, text='自动凝神术', bg=BG, fg=MUT, font=F(9))
    lb_heal.pack(side='left', padx=(3, 0))
    # ★ 2026-10-21：状态文字从这一行挪出去单独占一行 ——
    #   这一行现在有 复活 + 两个勾选 + 百分比下拉，中栏只有 ~508px，
    #   lb_atk 再挤在里面就只剩几十像素、连「未上线」都显示不全。
    lb_atk = tk.Label(lf_fight, text='未进入世界', bg=BG, fg=MUT, font=F(9),
                      anchor='w')
    lb_atk.pack(fill='x', padx=12, pady=(0, 8))

    # ---------------- 右栏：角色信息
    #   ★ 2026-10-21 第二次改版（用户要求）：
    #     ① 原来那 9 行文字（角色/账号/区服/分区/线路/职业/状态/血量蓝/已学技能）
    #        连同下方提示文字**整块去掉**，界面上只留「上线」「编辑」「删除」；
    #     ② 腾出来的位置放 **6 个「指定物品」格子，3 列 × 2 行**，
    #        样式跟技能格一致，用来盯背包里某几样东西还剩多少（药水/材料…）。
    #   ⚠ 那 9 个 label 旧代码到处 configure()，用 _NullLabel 桩接住。
    lf_rinfo = tk.LabelFrame(col2, text=' 角色信息 ', bg=BG, fg=FG,
                             font=F(10, 'bold'), bd=1, relief='groove')
    lf_rinfo.pack(fill='x', pady=(2, 0))

    lb_cur = lb_racct = lb_rarea = lb_rzone = lb_rline = _NullLabel()
    lb_rcls = lb_tst = lb_hp = lb_rsk = lb_rtip = _NullLabel()

    # —— 等级 / 经验（2026-10-21 新增：用户要求读出等级和经验）
    #   数据来自 0x60F PlayerExpUpdate 与 0x623 的 attr 5001/3009
    f_lv = tk.Frame(lf_rinfo, bg=BG)
    f_lv.pack(fill='x', padx=9, pady=(8, 0))
    lb_lv = tk.Label(f_lv, text='等级 —', bg=BG, fg=FG, font=F(10, 'bold'),
                     anchor='w')
    lb_lv.pack(side='left')
    lb_exp = tk.Label(f_lv, text='经验 —', bg=BG, fg=MUT, font=F(9),
                      anchor='e')
    lb_exp.pack(side='right')

    def _lv_show(d):
        """刷新等级 / 经验显示（经验条也在这里刷）"""
        _lv = d.get('lv')
        # ★ 兼容两种键名：事件里是 need，会话缓存里可能写成 expneed
        _e = d.get('exp')
        _n = d.get('need') or d.get('expneed')
        try:
            lb_lv.configure(text=('Lv.%d' % _lv) if _lv else '等级 —')
            if _e is None:
                lb_exp.configure(text='经验 —', fg=MUT)
                _bar_set(bar_exp, redraw_exp, None, 0)
            elif _n:
                _p = 100.0 * _e / _n if _n else 0.0
                lb_exp.configure(text='%.1f%%' % _p,
                                 fg=(GRN if _p >= 99.0 else FG))
                _bar_set(bar_exp, redraw_exp, _e, _n)
            else:
                lb_exp.configure(text='', fg=FG)
                _bar_set(bar_exp, redraw_exp, _e, 0)
        except Exception:
            pass

    # —— 血条 / 蓝条 / 经验条（2026-10-21 用户要求）
    #   红=血、蓝=法力、金=经验；中间写「当前 / 上限」，边框浅灰槽。
    #   数据仍然来自 0x623（attr 2008 血上限 / 2009 蓝上限）和
    #   0x60F+0x623 5001/3009（等级 / 经验），只是从文字改成条。
    def _mk_bar(parent, color, label):
        # ⚠ Tk 的 Canvas 不给 width 时默认请求 378px，pack(fill='x') 会把这个
        #   请求宽度传给父容器，右栏（318 定死）被撑破、还溢出到窗口外。
        #   这里显式给一个小宽度（180），实际显示仍由 fill='x' 拉满。
        cv = tk.Canvas(parent, width=180, height=15, bg='#D8D8D8', bd=0,
                       highlightthickness=0)
        cv.pack(fill='x', padx=9, pady=(4, 0))
        st = {'cur': 0, 'max': 0, 'txt': '%s —' % label, 'label': label,
              'color': color}

        def redraw(_e=None):
            try:
                w = cv.winfo_width()
                if w < 12:
                    return
                cv.delete('all')
                cv.create_rectangle(0, 0, w, 15, fill='#D8D8D8', outline='')
                mx = int(st['max'] or 0)
                cur = int(st['cur'] or 0)
                if mx > 0:
                    r = max(0.0, min(1.0, cur * 1.0 / mx))
                    if r > 0:
                        cv.create_rectangle(0, 0, max(1, int(w * r)), 15,
                                            fill=st['color'], outline='')
                # 文字先描一圈深色再写白字 —— 条的填充比例很小时文字会落在
                # 浅灰槽上，纯白看不清（经验 10% 就是这种情况）
                cv.create_text(w // 2 + 1, 9, text=st['txt'], fill='#3A3A3A',
                               font=F(8, 'bold'))
                cv.create_text(w // 2, 8, text=st['txt'], fill='#FFFFFF',
                               font=F(8, 'bold'))
            except Exception:
                pass

        cv.bind('<Configure>', redraw)
        return cv, st, redraw

    cv_hp, bar_hp, redraw_hp = _mk_bar(lf_rinfo, '#C62828', '血')
    cv_mp, bar_mp, redraw_mp = _mk_bar(lf_rinfo, '#1565C0', '蓝')
    cv_exp, bar_exp, redraw_exp = _mk_bar(lf_rinfo, '#C85A10', '经验')

    def _bar_set(bar, redraw, cur, mx, suffix=''):
        bar['cur'] = int(cur or 0)
        bar['max'] = int(mx or 0)
        if cur is None and not mx:
            bar['txt'] = '%s —' % bar['label']
        elif mx:
            bar['txt'] = '%s %s / %s%s' % (
                bar['label'],
                '{:,}'.format(int(cur or 0)), '{:,}'.format(int(mx)), suffix)
        else:
            bar['txt'] = '%s %s' % (bar['label'],
                                    '{:,}'.format(int(cur or 0)))
        redraw()


    #   ★ 2026-10-21 改版（用户要求）：格子 48×48，背景用背包背景图；
    #     点格子只能从 时装图标/（Fashion9，即 icons_full/Fashion9 那 64 个箱子）里选。
    #     用户不知道这些箱子的物品 ID，所以这里让他**看图点选**，不用记 ID。
    g_wrap = tk.Frame(lf_rinfo, bg=BG)
    g_wrap.pack(fill='x', padx=9, pady=(9, 2))
    g_item = tk.Frame(g_wrap, bg=BG)
    g_item.pack(anchor='center')

    # ★ 2026-10-21 用户要求格子保持 48。但用户给的宝箱图标是 64x64，
    #   直接塞进 48 格子会被 Canvas 裁掉四边（金框都没了）。
    #   Tk 只能整数倍缩放，所以按整数倍 subsample 到 ≤48：
    #     64 -> 32（subsample 2）、96 -> 48（subsample 2）、128 -> 32（subsample 4）
    ITEM_W, ITEM_H = 48, 48
    slots_item = []
    _items0 = load_items()

    # 格子底图（48×48 预缩放版，随 时装图标/ 一起走）
    _bg_img = None
    _fdir = _fash9_dir()
    if _fdir:
        _bp = os.path.join(_fdir, '_bg48.png')
        if os.path.exists(_bp):
            try:
                _bg_img = tk.PhotoImage(file=_bp)
            except Exception:
                _bg_img = None

    def _item_paint(w):
        """重画一个物品格

        ★ 2026-10-21 用户要求：**读到物品就不要背景了，自动隐藏背景**。

          原因（实测截图）：背包底图是深色的，而物品名用的是深色字
          （FG = #1A1A1A），压在底图上完全看不见 —— 界面上只剩个数量角标，
          看起来像"物品没读出来"。所以现在分两种画法：

            空格子  → 铺背包背景（_bg48.png），一眼看出这是空槽
            有物品  → **不画背景**：有图标就只放图标（图标自带金边框）；
                      没图标就铺白底 + 深色名字，保证文字一定能看清
        """
        cv = w['cv']
        try:
            cv.delete('all')
            iid = int(w.get('iid') or 0)

            if not iid:
                # —— 空格子：铺背包背景
                if w.get('bg') is not None:
                    cv.create_image(0, 0, anchor='nw', image=w['bg'])
                else:
                    cv.create_rectangle(0, 0, ITEM_W - 1, ITEM_H - 1,
                                        fill='#232323', outline='#5A5A5A')
                return

            # —— 有物品：不要背景（否则会盖住素材/名字）
            # ★★★ 2026-10-21 用户定案：图标**只从 `技能图标\` 那批按名字命名的
            #   png 里取**（如「神风分坛地灵宝箱.png」）。名字对上就用，
            #   对不上就白底写名字。不再走配置表图标、不再有任何缓存目录。
            img = box_icon_photo(item_name(iid))
            if img is not None:
                w['icon'] = img        # 必须留引用，否则图会被回收
                cv.create_image(ITEM_W // 2, ITEM_H // 2, image=img)
            else:
                # 没有 Fashion9 图标（比如普通宝箱）→ 白底 + 深色名字
                cv.create_rectangle(1, 1, ITEM_W - 2, ITEM_H - 2,
                                    fill='#FFFFFF', outline='#A8A8A8')
                _t = item_name(iid) or ('#%d' % iid)
                cv.create_text(ITEM_W // 2, ITEM_H // 2, text=_t[:4],
                               fill=FG, font=F(8), width=ITEM_W - 6,
                               justify='center')

            _n = int(w.get('n') or 0)
            if _n > 0:
                # 数量：右下角，垫一块黑底再写白字 —— 压在物品名/图标上都看得清
                _s = str(_n)
                _tx, _ty = ITEM_W - 1, ITEM_H - 1
                _bw = 5 + 4 * len(_s)
                cv.create_rectangle(_tx - _bw, _ty - 12, _tx, _ty,
                                    fill='#101010', outline='')
                cv.create_text(_tx - 2, _ty - 1, text=_s, anchor='se',
                               fill='#FFFFFF', font=F(7, 'bold'))
        except Exception:
            pass

    def _item_click(idx):
        """点格子只显示信息 —— 箱子是**自动识别**的，不需要手动挑"""
        w = slots_item[idx]
        iid = int(w.get('iid') or 0)
        if not iid:
            log('[*] 物品格 #%d：空（背包里暂时没识别到箱子）' % (idx + 1))
            return
        log('[*] 物品格 #%d：%s  物品 %d  数量 %d'
            % (idx + 1, item_name(iid) or fash9_icon_of(iid) or '?', iid,
               int(w.get('n') or 0)))

    # ---- 使用物品（右键菜单）
    def _st_online():
        """当前选中的角色是否在世界里（没上线就没法用物品）"""
        try:
            s = sess()
            return bool(s) and (s.get('state') == 'online')
        except Exception:
            return False

    def _use_once(idx):
        w = slots_item[idx]
        iid = int(w.get('iid') or 0)
        if not iid:
            return
        slot, cont = int(w.get('slot') or 0), int(w.get('cont') or 1)
        log('[*] 使用「%s」×1（槽位 %d）'
            % (item_name(iid) or ('#%d' % iid), slot))
        try:
            client.post('use_once', slot=slot, iid=iid, cont=cont)
        except Exception as ex:
            log('[!] 使用物品失败：%s' % ex)

    def _use_until_empty(idx):
        w = slots_item[idx]
        iid = int(w.get('iid') or 0)
        if not iid:
            return
        slot, cont = int(w.get('slot') or 0), int(w.get('cont') or 1)
        n = int(w.get('n') or 0)
        log('[*] 循环使用「%s」（当前 %d 个，槽位 %d）'
            % (item_name(iid) or ('#%d' % iid), n, slot))
        try:
            client.post('use_loop', slot=slot, iid=iid, cont=cont)
        except Exception as ex:
            log('[!] 使用物品失败：%s' % ex)

    def _item_menu(idx):
        w = slots_item[idx]
        m = tk.Menu(root, tearoff=0)
        iid = int(w.get('iid') or 0)
        if iid:
            m.add_command(label='%s（物品 %d）'
                                % (item_name(iid) or fash9_icon_of(iid) or '?', iid),
                          state='disabled')
            m.add_command(label='数量 %d' % int(w.get('n') or 0), state='disabled')
        else:
            m.add_command(label='空格（背包里没识别到箱子）', state='disabled')
        m.add_separator()
        # ★ 2026-10-21 用户要求：右键弹「使用一次 / 用完为止」
        _can = bool(iid) and int(w.get('slot') or 0) >= 0 and _st_online()
        if iid:
            m.add_command(label='使用一次',
                          command=lambda i=idx: _use_once(i),
                          state=('normal' if _can else 'disabled'))
            m.add_command(label='用完为止',
                          command=lambda i=idx: _use_until_empty(i),
                          state=('normal' if _can else 'disabled'))
            if not _can:
                m.add_command(label='（角色未上线，用不了）', state='disabled')
        else:
            m.add_command(label='使用一次', state='disabled')
            m.add_command(label='用完为止', state='disabled')
        m.add_separator()
        m.add_command(label='重新读取背包',
                      command=lambda: _bag_refresh())
        try:
            m.tk_popup(root.winfo_pointerx(), root.winfo_pointery())
        finally:
            m.grab_release()

    def _bag_refresh():
        """手动让当前角色重读一次背包（万一服务端漏发了 0x613）"""
        try:
            client.post('bag')
            log('[*] 已请求重新读取背包…')
        except Exception as ex:
            log('[!] 请求背包失败：%s' % ex)

    def _fill_boxes(boxes):
        """把自动识别到的箱子按顺序铺进 6 个格子（含数量）

        ★ 2026-10-21 用户要求：自动识别、不用点选、要显示数量。
          多出来的箱子不丢，日志里提示一共有几个。
        """
        boxes = boxes or []
        for i in range(N_ITEM_SLOT):
            w = slots_item[i]
            if i < len(boxes):
                b = boxes[i]
                w['iid'] = int(b.get('iid') or 0)
                w['n'] = int(b.get('n') or 0)
                w['slot'] = int(b.get('slot') or 0)
                w['cont'] = int(b.get('cont') or 1)
                w['fash'] = fash9_icon_of(w['iid'])
            else:
                w['iid'] = 0
                w['n'] = 0
                w['slot'] = 0
                w['cont'] = 1
                w['fash'] = ''
            _item_paint(w)
        s = sess()
        s['boxes'] = boxes
        if len(boxes) > N_ITEM_SLOT:
            log('[*] 背包里识别到 %d 个箱子，只显示前 %d 个（其余略）'
                % (len(boxes), N_ITEM_SLOT))

    def _item_tip_show(idx):
        w = slots_item[idx]
        iid = int(w.get('iid') or 0)
        if not iid:
            lb_atk.configure(text='物品格 #%d：空（背包里没识别到箱子）'
                                  % (idx + 1), fg=MUT)
            return
        _n = int(w.get('n') or 0)
        lb_atk.configure(
            text='物品格 #%d：%s  物品 %d %s  数量 %d'
                 % (idx + 1, item_name(iid) or fash9_icon_of(iid) or '?', iid,
                    item_name(iid) or '', _n),
            fg=FG)

    def _item_tip_hide():
        pass

    def _item_make(idx, iid0):
        cv = tk.Canvas(g_item, width=ITEM_W, height=ITEM_H, bd=0,
                       highlightthickness=0, bg=BG, cursor='hand2')
        cv.grid(row=idx // 3, column=idx % 3, padx=3, pady=3)
        w = {'cv': cv, 'bg': _bg_img, 'icon': None, 'cnt_on': False,
             'iid': int(iid0 or 0), 'fash': '', 'idx': idx, 'n': 0}
        cv.bind('<Button-1>', lambda e, i=idx: _item_click(i))
        cv.bind('<Button-3>', lambda e, i=idx: _item_menu(i))
        cv.bind('<Enter>', lambda e, i=idx: _item_tip_show(i))
        cv.bind('<Leave>', lambda e: _item_tip_hide())
        return w

    for _i in range(N_ITEM_SLOT):
        slots_item.append(_item_make(_i, _items0[_i]))

    def load_items_for(key):
        """切换/刷新角色：用这个角色**已经收到的**箱子清单重画这 6 格

        ★★★ 2026-10-21 修（用户反馈 v4.6「刚才还能读出背包，这版读不出来了」）：
          上一版这里是无条件清空，等着 0x613 来填。但 `apply_cur` 会在很多时机
          被调用（点角色、上线状态变化、切页…），只要它跑在 bag_box 事件之后，
          就会把刚填好的格子抹掉；而 0x613 是**进世界时一次性下发**的，不会
          重发 → 格子从此永远空白，只有重启角色才可能再碰上好时序。

          现在改成从会话里缓存的 s['boxes'] 恢复 —— 事件先到后到都不丢。
        """
        s = SESS.get(key) or {}
        _fill_boxes(s.get('boxes') or [])

    for _w in slots_item:
        _item_paint(_w)

    # —— 三个按钮：上线/下线、编辑、删除
    f_rbtn = tk.Frame(lf_rinfo, bg=BG)
    f_rbtn.pack(fill='x', padx=8, pady=(6, 4))
    btn_online = ttk.Button(f_rbtn, text='上  线', style='FB.TButton')
    btn_online.pack(fill='x')
    f_rbtn2 = tk.Frame(lf_rinfo, bg=BG)
    f_rbtn2.pack(fill='x', padx=8, pady=(0, 8))
    btn_redit = ttk.Button(f_rbtn2, text='编辑', width=8, style='MB.TButton')
    btn_redit.pack(side='left')
    btn_rdel = ttk.Button(f_rbtn2, text='删除', width=8, style='MB.TButton')
    btn_rdel.pack(side='right')

    # ---------------- 右栏：多开时一键批量
    lf_rbatch = tk.LabelFrame(col2, text=' 批量 ', bg=BG, fg=FG,
                              font=F(10, 'bold'), bd=1, relief='groove')
    lf_rbatch.pack(fill='x', pady=(10, 0))
    f_bb2 = tk.Frame(lf_rbatch, bg=BG)
    f_bb2.pack(fill='x', padx=7, pady=7)
    btn_all_on = ttk.Button(f_bb2, text='全部上线', style='MB.TButton')
    btn_all_on.pack(side='left', expand=True, fill='x', padx=(0, 3))
    btn_all_off = ttk.Button(f_bb2, text='全部下线', style='MB.TButton')
    btn_all_off.pack(side='left', expand=True, fill='x', padx=(3, 0))

    # ---------------- 左栏：传送到位（0x407）
    f_tp = tk.LabelFrame(col2, text=' 传送到位（0x407） ', bg=BG, fg=FG,
                         font=F(10, 'bold'), bd=1, relief='groove')
    f_tp.pack(fill='x', pady=(10, 0))
    g_tp = tk.Frame(f_tp, bg=BG)
    g_tp.pack(fill='x', padx=6, pady=2)
    g_tp.columnconfigure(1, weight=1)

    def _xy_row(row, text, defval):
        tk.Label(g_tp, text=text, bg=BG, fg=FG, font=F(10)).grid(
            row=row, column=0, sticky='w', pady=4)
        e = tk.Entry(g_tp, font=F(11), width=11)
        e.insert(0, defval)
        e.grid(row=row, column=1, sticky='we', ipady=3, pady=4, padx=(8, 0))
        return e

    e_gx = _xy_row(0, 'X', '4457')
    e_gy = _xy_row(1, 'Y', '4589')
    tk.Label(g_tp, text='Z', bg=BG, fg=FG, font=F(10)).grid(
        row=2, column=0, sticky='w', pady=4)
    e_gz = tk.Entry(g_tp, font=F(11), width=11)
    e_gz.insert(0, '0')
    e_gz.grid(row=2, column=1, sticky='we', ipady=3, pady=4, padx=(8, 0))
    tk.Label(g_tp, text='（Z 一般填 0）', bg=BG, fg=MUT,
             font=F(9)).grid(row=3, column=0, columnspan=2, sticky='w', pady=(0, 2))

    lb_tp = tk.Label(f_tp, text='未进入世界', bg=BG, fg=MUT, font=F(9),
                     anchor='w', justify='left', wraplength=292)
    lb_tp.pack(fill='x', padx=8, pady=(2, 0))

    btn_goto = ttk.Button(f_tp, text='传  送', style='FB.TButton')
    btn_goto.pack(fill='x', padx=7, pady=(4, 8))


    # ---------------------------------------------------------- 底部：日志 + 按钮
    bottom = tk.Frame(root, bg=BG)
    bottom.pack(fill='x', padx=8, pady=(0, 8))
    f_log = tk.Frame(bottom, bg=PANEL, bd=1, relief='solid')
    f_log.pack(side='left', fill='both', expand=True)
    txt = tk.Text(f_log, height=3, font=F(9), bg=PANEL, fg=FG,
                  relief='flat', wrap='none')
    sbl = ttk.Scrollbar(f_log, orient='vertical', command=txt.yview)
    txt.configure(yscrollcommand=sbl.set)
    txt.pack(side='left', fill='both', expand=True, padx=3, pady=2)
    sbl.pack(side='right', fill='y')
    txt.configure(state='disabled')

    f_bb = tk.Frame(bottom, bg=BG)
    f_bb.pack(side='right', fill='y', padx=(10, 0))
    btn_quit = ttk.Button(f_bb, text='退出程序', width=12, style='FB.TButton')
    btn_quit.pack(pady=3)

    # ================================================================ 逻辑
    AREAS, ZONES, ROLES = [], [], []
    CHK = {}                      # 角色ID → 是否勾选
    ZONE_OF = {}                  # 分区名 → 0x117 dict
    WLINE = []
    task = {'active': False, 't0': 0.0, 'dur': 0, 'role': ''}
    stamp = {}

    def _log_ui(line):
        """只往界面文本框里写一行（已经带好时间戳）"""
        txt.configure(state='normal')
        txt.insert('end', line + '\n')
        txt.see('end')
        txt.configure(state='disabled')

    def log(s):
        # ★ 2026-10-21：界面日志以前只进文本框不进文件，导致「已选中/技能格
        #   换位」这类操作在日志里查不到（排障时以为功能没触发）。现在两边都写。
        # ⚠ 但客户端线程产生的日志**已经写过一次文件**了，事件泵里转发到界面
        #   时必须走 _log_ui，不能再写一遍 —— 否则日志每一行都是两条。
        line = '[%s] %s' % (time.strftime('%H:%M:%S'), s)
        _log_ui(line)
        if _LOGF is not None:
            try:
                _LOGF.write(line + '\n')
                _LOGF.flush()
            except Exception:
                pass

    def safe(fn, tag):
        """★ 把界面回调包一层。打包成无控制台 exe 后，回调里抛异常是"完全无声"的
        （用户只会觉得按钮点了没反应），所以统一捕获并写进日志。"""
        def wrapper(*a, **k):
            try:
                return fn(*a, **k)
            except Exception as ex:
                import traceback
                log('[!] %s 出错：%s' % (tag, ex))
                try:
                    log('    ' + traceback.format_exc().strip().splitlines()[-1])
                except Exception:
                    pass
        return wrapper

    def clock_str(t0):
        d = max(0, int(time.time() - t0))
        return '%02d:%02d' % (d // 60, d % 60)

    # ============================================ 左栏：录入流程（只动 pc）
    SEL = '#D4E6F8'
    # ★ 2026-10-21 多线程录入：登录过程中把按钮置灰。
    #   以前点完登录界面毫无变化（后台在排队/连服务器），用户以为没反应就连点，
    #   队列里堆一串 logout/login，反而更难连上。
    LOGIN_UI = {'busy': False}

    # 失败计数（只用来提示，**绝不拦人**）
    # ★★★ 2026-10-21 修正：上一版根据一次 WinError 10054 就推断"服务端限流"，
    #   然后 5 分钟失败 3 次就弹窗硬拦，不让用户点登录 —— 这是过度设计，
    #   而且证据不足：10054 也可能只是那一次网络瞬断 / 服务端重启连接。
    #   现在只统计、只在日志里提示，**永远返回 True，绝不阻止用户操作**。
    FAIL_HIST = []
    FAIL_WINDOW = 300.0
    FAIL_LIMIT = 3

    def fail_note():
        FAIL_HIST.append(time.time())

    def net_guard():
        """连接前的一句提醒（不拦人）。永远放行。"""
        now = time.time()
        FAIL_HIST[:] = [t for t in FAIL_HIST if now - t < FAIL_WINDOW]
        if len(FAIL_HIST) >= FAIL_LIMIT:
            log('[i] 最近 %d 分钟内失败了 %d 次。若一直连不上，可先全部关掉'
                '游戏客户端/启动器，并确认同账号没有别的连接在跑'
                % (int(FAIL_WINDOW // 60), len(FAIL_HIST)))
        return True

    # ★ 2026-10-21 补回：这两个原来在 reset_steps 上面，重构时被连带删掉了，
    #   结果「选完区服读角色」直接 NameError: selected_zone is not defined。
    def selected_zone():
        """当前选中的分区（0x117 dict），没选返回 None"""
        i = cb_zone.current()
        if i < 0 or i >= len(ZONES):
            return None
        return ZONES[i]

    def selected_area_name():
        """当前选中的大区名（写进档案用）"""
        i = cb_area.current()
        return AREAS[i]['name'] if 0 <= i < len(AREAS) else ''

    def repaint_slots():
        for s in slots:
            sel = bool(s.get('sel'))
            s['row'].configure(bg=(SEL if sel else BG))
            s['name'].configure(bg=(SEL if sel else BG))
            s['no'].configure(bg=(SEL if sel else BG), fg=(RED if sel else FG))
            if s['role'] is None:
                s['btn'].configure(text='创建')
            else:
                # 未选中显示「选中」，选中了给个对勾（线路不读了，没「换线」了）
                s['btn'].configure(text=('\u2714' if sel else '选中'))

    def clear_slots_ui():
        """只清左栏那 4 个槽位，不动中间的档案列表"""
        del ROLES[:]
        for s in slots:
            s['role'] = None
            s['sel'] = False
            s['name'].configure(text='空', fg=MUT)
        try:
            repaint_slots()
        except Exception:
            pass

    def reset_probe_ui():
        """把左栏「录入」整块退回**刚打开程序的样子**。

        ★ 2026-10-21 用户要求：「点了录入这套流程就该走完了，自动退」。
          以前录完只是断了连接，大区/分区/角色/线路还留在界面上，
          看着像流程没结束，而且再点角色还会报「请先登录账号」。
          现在录完直接复位（账号密码保留，方便连续录同一个账号的角色）。
        """
        del AREAS[:]
        del ZONES[:]
        del ROLES[:]
        ZONE_OF.clear()
        try:
            cb_area.set('')
            cb_area['values'] = []
            cb_zone.set('')
            cb_zone['values'] = []
            del WLINE[:]
            cb_line.set('')
            cb_line['values'] = []
            cb_line.configure(state='disabled')
        except Exception:
            pass
        for sj in slots:
            sj['role'] = None
            sj['sel'] = False
            sj['name'].configure(text='空', fg=MUT)
            sj['btn'].configure(text='创建')
        try:
            repaint_slots()
        except Exception:
            pass
        # 复位 = 这一次录入流程结束了，登录按钮恢复可点
        LOGIN_UI['busy'] = False
        try:
            btn_login.configure(state='normal', text='登  录')
        except Exception:
            pass

    def fill_areas(areas):
        del AREAS[:]
        AREAS.extend(areas)
        cb_area['values'] = [a['name'] for a in areas]
        # ★ 登录成功后大区留空，等用户自己选；不自动选第一个、更不自动去读角色
        cb_area.set('')
        del ZONES[:]
        cb_zone.set('')
        cb_zone['values'] = []
        clear_slots_ui()
        log('大区列表已就绪（%d 个）—— 请选择「大区信息」' % len(areas))

    def on_area(_=None):
        """选大区 → 只刷新「分区」列表，不动网络"""
        del ZONES[:]
        cb_zone.set('')
        cb_zone['values'] = []
        clear_slots_ui()
        i = cb_area.current()
        if i < 0:
            return
        aid = AREAS[i]['id']
        for ln in pc.lines:
            if ln['area'] == aid:
                ZONES.append(ln)
        cb_zone['values'] = [z['name'] for z in ZONES]
        if ZONES:
            log('大区「%s」：%d 个分区 —— 请选择「分区」' % (AREAS[i]['name'], len(ZONES)))
        else:
            log('大区「%s」下没有分区' % AREAS[i]['name'])

    # ---- 选分区 → 这时才去读角色（+ 线路）
    def on_zone(_=None):
        z = selected_zone()
        if z is None:
            return
        if pc.ls is None:
            log('[!] 请先登录账号')
            return
        # ★★★ 服务端限制：一条 World 连接只能连一个分区，而且同账号释放极慢。
        #   所以：**选到原来那个分区就直接复用**（角色立刻出来，不重连）；
        #   选别的分区才提示重新登录。
        # ★★★ 2026-10-21 多线程录入：复用旧结果前必须**校验账号**。
        #   以前只看 pc.w + 分区名，不看 pc._acct 是不是输入框里这个账号 ——
        #   上个账号的 World 还没断干净时换账号选同一个分区，就会把
        #   **上一个账号的角色列表**铺给新账号；点「录入」得到一条
        #   角色名 / cid / rid 全属于上个账号的错档案，上线时怎么都匹配不上。
        _ac = (e_acct.get() or '').strip()
        _pc_ac = (getattr(pc, '_acct', '') or '').strip()
        if pc.w is not None and pc.cur_line is not None and _pc_ac == _ac:
            if (pc.cur_line.get('name') or '') == (z.get('name') or ''):
                if pc.roles:
                    fill_probe_roles(list(pc.roles))
                    log('[*] 这个分区已经读过角色了（%d 个）—— 直接点选，不用重连'
                        % len(pc.roles))
                    return
            else:
                log('[!] 换分区必须重新登录（一条 World 连接只连一个分区）—— '
                    '点「登 录」重新走一遍。')
                names = [x['name'] for x in ZONES]
                if (pc.cur_line.get('name') or '') in names:
                    cb_zone.current(names.index(pc.cur_line['name']))
                return
        if not net_guard():
            return
        clear_slots_ui()
        for s_ in slots:
            s_['name'].configure(text='读取中…', fg=MUT)
        log('[*] 分区「%s」→ 正在读取角色…' % z['name'])
        pc.post('loadroles', line=z)

    # ---- 登录（录入的前置步骤）
    def on_login():
        acct = e_acct.get().strip()
        pwd = e_pwd.get().strip()
        if not acct:
            messagebox.showwarning('提示', '先把账号填上')
            return
        if LOGIN_UI['busy']:
            log('[*] 上一条登录还在进行中，请稍等（多线程录入是排队连接的）…')
            return
        if not net_guard():
            return
        reset_probe_ui()

        # ★★★ 2026-10-21 连接池复用：这个账号之前录过、连接还挂在闲置池里，
        #   直接拿回来用，**不发任何登录/World 包**。
        #   原因见 PARK 那段注释：服务端对同账号的 World 会话释放极慢，
        #   25 秒内重连连 0x20C 都不回，复用是唯一不会撞冷却的做法。
        old_cur = PROBE.get('cur')
        reused = unpark_probe(acct)
        if reused is not None:
            PROBE['cur'] = reused
            if old_cur is not None and old_cur is not reused:
                park_probe(old_cur)
            LOGIN_UI['busy'] = False
            try:
                btn_login.configure(state='normal', text='登  录')
            except Exception:
                pass
            try:
                fill_areas(list(reused.areas or []))
            except Exception:
                pass
            log('[*] 复用账号「%s」已登录的连接（%d 个分区）—— 直接选大区/分区，'
                '不用重新登录' % (acct, len(reused.lines or [])))
            if reused.cur_line is not None and reused.roles:
                log('   （上次停在分区「%s」，已读到 %d 个角色，选回同一个分区就直接出来）'
                    % (reused.cur_line.get('name') or '?', len(reused.roles)))
            return

        LOGIN_UI['busy'] = True
        try:
            btn_login.configure(state='disabled', text='登录中…')
        except Exception:
            pass

        def _go():
            cl = new_probe(acct)
            log('[*] 登录账号「%s」（独立连接 %s）…' % (acct, cl.tag))
            cl.post('login', host=LOGIN_HOST_DEF, port=LOGIN_PORT_DEF,
                    acct=acct, pwd=pwd)

        # ★ 要断掉别的账号的旧连接时，先等它真的关完再连新的。
        #   这 1.5 秒不是"限流等待"，是让 close() 走完 —— 否则新连接会和
        #   正在关闭的旧连接抢同一个名额，又变成 flag=1。
        #   ⚠ 刚启动时那条 boot 连接 _acct 是空的，不算"别的账号"，别白等。
        _wait = False
        _c = PROBE.get('cur')
        _cac = (getattr(_c, '_acct', '') or '').strip() if _c is not None else ''
        if _cac and _cac != acct:
            _wait = True
        for _o in PARK:
            _oac = (getattr(_o, '_acct', '') or '').strip()
            if _oac and _oac != acct:
                _wait = True
                break
        if _wait:
            log('[*] 先断开上一个账号的录入连接，1.5 秒后登录「%s」…' % acct)
            root.after(1500, safe(_go, '登录'))
        else:
            _go()

    # ---- 角色槽位：点击选中；选中后才读线路，按钮才显示「换线」
    def pick_slot(idx):
        """点角色 = 只在这里选中它，**不发选角包**。

        ★★★ 2026-10-21 关键修正（用户：不能让第一个角色一直占着位置）
          以前点角色会发 0x205 选角去读线路，服务端从那一刻起就把这个角色
          记成"已登录"，即使只退回角色选择（0x210）也不一定马上释放 ——
          于是同账号再连 World 直接被关。
          现在录入**压根不选角**：角色列表是 0x205 请求回来的，不需要选；
          线路也不要了（上线时 do_enter 自己会选角读线路，默认第 1 条）。
          这样这条连接从头到尾没有任何角色被占用，断开后账号是干净的。
        """
        s = slots[idx]
        if s['role'] is None:
            return
        for k, o in enumerate(slots):
            o['sel'] = (k == idx)
        repaint_slots()
        try:
            e_role.delete(0, 'end')
            e_role.insert(0, s['role']['name'])
        except Exception:
            pass
        log('[*] 已选中「%s」—— 名字已填到上面，点「录 入」保存'
            % s['role']['name'])

    # ---- 换线：弹出线路列表，点中哪条才算
    pending_menu = [None]
    cur_menu = [None]

    def do_switch(idx, i):
        s = slots[idx]
        if not s['role'] or not (0 <= i < len(WLINE)):
            return
        for k, o in enumerate(slots):
            o['sel'] = (k == idx)
        repaint_slots()
        try:
            cb_line.current(i)
        except Exception:
            pass
        log('[*] 已选定：角色「%s」＋线路「%s」—— 点「录 入」保存'
            % (s['role']['name'], WLINE[i]['name']))

    def pop_lines_menu(idx):
        s = slots[idx]
        if not s['role']:
            return
        if not WLINE:
            log('[!] 还没有线路信息，请稍后重试')
            return
        if cur_menu[0] is not None:
            try:
                cur_menu[0].unpost()
                cur_menu[0].destroy()
            except Exception:
                pass
            cur_menu[0] = None
        menu = tk.Menu(root, tearoff=0, font=F(10))
        cur_menu[0] = menu
        for i, wl in enumerate(WLINE):
            menu.add_command(
                label=wl['name'],
                command=safe(lambda i=i: do_switch(idx, i), '执行换线'))
        menu.add_separator()
        menu.add_command(label='取消', command=lambda: None)
        b = s['btn']
        try:
            menu.tk_popup(b.winfo_rootx(),
                          b.winfo_rooty() + b.winfo_height())
        finally:
            try:
                menu.grab_release()
            except Exception:
                pass

    def bind_slot(idx):
        s = slots[idx]

        def _pick(_=None):
            pick_slot(idx)

        def _act():
            if s['role'] is None:
                messagebox.showinfo('创建角色', '创建角色需在游戏客户端内完成，本工具暂未实现。')
                return
            pick_slot(idx)

        s['btn'].configure(command=safe(_act, '选中/创建 按钮'))
        for w in (s['row'], s['no'], s['name']):
            w.bind('<Button-1>', safe(_pick, '角色槽位点击'))

    for _i in range(4):
        bind_slot(_i)
    repaint_slots()

    def fill_probe_roles(roles):
        """pc 读到角色 → 只填左栏 4 个槽位（中间列表是档案，不受影响）"""
        del ROLES[:]
        ROLES.extend(roles)
        for k, sj in enumerate(slots):
            if k < len(roles):
                sj['role'] = roles[k]
                sj['name'].configure(text=roles[k]['name'], fg=FG)
            else:
                sj['role'] = None
                sj['sel'] = False
                sj['name'].configure(text='空', fg=MUT)
        repaint_slots()

    # ============================================ 中间：角色档案列表
    def row_by_key(key):
        for r in ARCH:
            if r.get('key') == key:
                return r
        return None

    def state_text(row):
        s = SESS.get(row.get('key')) or {}
        st = s.get('state') or 'offline'
        return {'offline': '未上线', 'login': '登录中', 'world': '连接中',
                'entering': '进入中', 'online': '在线', 'error': '出错'
                }.get(st, st)

    def render_arch():
        """按 ARCH 重画中间列表（尽量保住当前选中行和滚动位置）"""
        keep = CUR['key']
        tv.delete(*tv.get_children())
        for row in ARCH:
            s = SESS.get(row.get('key')) or {}
            cls = cls_of(s) if s.get('learned') else (row.get('cls') or '—')
            try:
                tv.insert('', 'end', iid=row.get('key'),
                          values=(row.get('name') or '', row.get('acct') or '',
                                  row.get('zone') or '', cls, state_text(row)))
            except Exception:
                pass
        if keep and tv.exists(keep):
            try:
                tv.selection_set(keep)
                tv.see(keep)
            except Exception:
                pass

    def hp_mp_text(s):
        """刷新血条 / 蓝条（原来那行文字已改成条）"""
        if s.get('state') != 'online':
            lb_hp.configure(text='—', fg=MUT)
            _bar_set(bar_hp, redraw_hp, None, 0)
            _bar_set(bar_mp, redraw_mp, None, 0)
            return
        if s.get('dead'):
            lb_hp.configure(text='已死亡', fg=RED)
            _bar_set(bar_hp, redraw_hp, 0, int(s.get('hpmax') or 0))
            _bar_set(bar_mp, redraw_mp, s.get('mp'), s.get('mpmax'))
            return
        hp, mx = s.get('hp'), s.get('hpmax')
        mp, mm = s.get('mp'), s.get('mpmax')
        _bar_set(bar_hp, redraw_hp, hp, mx)
        _bar_set(bar_mp, redraw_mp, mp, mm)
        txt = '%s / %s' % (hp if hp is not None else '?',
                           mx if mx else '?')
        if mp is not None:
            txt += '   蓝 %s/%s' % (mp, mm or '?')
        lb_hp.configure(text=txt,
                        fg=RED if (hp is not None and mx and hp * 100.0 / mx < 30)
                        else FG)

    def load_slots_for(key):
        """把该角色的技能格绑定装进界面（切换角色时调）

        ★ 2026-10-21：绿框（选中参与连招的格子）也按角色记忆 ——
          先把上一个角色的选中状态存进 sel_memo，再恢复这个角色的。
          以前这里是无条件 slot_sel.clear()，所以点另一个角色回来绿框就没了。
        """
        _k = str(key) if key else '__none__'
        _prev = last_slot_key['v']
        if _prev is not None:
            sel_memo[_prev] = set(slot_sel)      # 记下上一个角色的绿框
        last_slot_key['v'] = _k
        a, b = load_slots(key)
        for w, sid in zip(slots_atk, a):
            w['sid'] = int(sid or 0)
        for w, sid in zip(slots_buf, b):
            w['sid'] = int(sid or 0)
        try:
            slot_sel.clear()
            # 只恢复「这个格子里确实还有技能」的下标（空格的绿框没意义）
            for _i in (sel_memo.get(_k) or ()):
                if 0 <= _i < len(slots_atk) and slots_atk[_i]['sid']:
                    slot_sel.add(_i)
        except Exception:
            pass
        try:
            _slot_paint_all()
        except Exception:
            pass

    def apply_cur():
        """切换/刷新选中角色要显示的一切：右侧信息 + 技能格 + 怪物 + 血蓝"""
        row = row_by_key(CUR['key'])
        s = sess()
        if not row:
            for lb in (lb_cur, lb_racct, lb_rarea, lb_rzone, lb_rline,
                       lb_rcls, lb_rsk):
                lb.configure(text='—')
            lb_tst.configure(text='未选中', fg=MUT)
            lb_hp.configure(text='—', fg=MUT)
            btn_online.configure(text='上  线')
        else:
            lb_cur.configure(text=row.get('name') or '—')
            lb_racct.configure(text=row.get('acct') or '—')
            lb_rarea.configure(text=row.get('area') or '—')
            lb_rzone.configure(text=row.get('zone') or '—')
            lb_rline.configure(text=row.get('line') or '默认线路')
            lb_rcls.configure(text=(cls_of(s) if s.get('learned')
                                    else (row.get('cls') or '—')))
            _st = s.get('state') or 'offline'
            lb_tst.configure(text=state_text(row),
                             fg=(GRN if _st == 'online' else
                                 (WARN if _st in ('login', 'world', 'entering')
                                  else (RED if _st == 'error' else MUT))))
            lb_rsk.configure(text=('%d 个' % len(s.get('learned') or ()))
                             if s.get('learned') else '—')
            btn_online.configure(text='下  线' if _st == 'online' else '上  线')
            hp_mp_text(s)
        # ★ 2026-10-21：等级/经验跟着当前选中角色走
        _lv_show(s if row else {})
        load_slots_for(CUR['key'])
        # ★ 2026-10-21：物品格也跟着当前角色走（每个角色一套配置）
        try:
            load_items_for(CUR['key'])
        except Exception:
            pass
        try:
            _draw_npcs(s.get('npcs') or [])
        except Exception:
            pass
        _on = bool(s.get('auto'))
        auto_state['on'] = _on
        try:
            btn_go.configure(text='停止' if _on else '开始')
        except Exception:
            pass
        # ★ 2026-10-21：自动同意组队的勾选状态跟着当前选中角色走
        #   （每个角色独立开关，切换角色不能串）
        try:
            var_team.set(bool(s.get('team')))
        except Exception:
            pass
        # ★ 2026-10-21：低血蓝自动凝神术的勾选 + 阈值也跟着当前角色走
        try:
            var_heal.set(bool(s.get('heal')))
            var_heal_pct.set('%d%%' % int(s.get('heal_pct') or 30))
        except Exception:
            pass
        try:
            lb_tp.configure(text=('已上线，可传送' if s.get('state') == 'online'
                                  else '未进入世界'),
                            fg=(MUT if s.get('state') != 'online' else FG))
        except Exception:
            pass
        _stt = s.get('state')
        lb_atk.configure(
            text=('在线 · 点「开始」按连招自动打怪' if _stt == 'online'
                  else ('正在上线…' if _stt in ('login', 'world', 'entering')
                        else ('× ' + (s.get('msg') or '上线失败')
                              if _stt == 'error' else '未上线'))),
            fg=(GRN if _stt == 'online' else
                (WARN if _stt in ('login', 'world', 'entering') else MUT)))

    def on_tv_select(_ev=None):
        sel = tv.selection()
        key = sel[0] if sel else None
        if key == CUR['key']:
            return
        CUR['key'] = key
        apply_cur()

    def select_arch_key(key):
        CUR['key'] = key
        if key and tv.exists(key):
            try:
                tv.selection_set(key)
                tv.see(key)
            except Exception:
                pass
        apply_cur()

    # ---- 录入：把左栏选好的角色存成档案
    def on_record():
        z = selected_zone()
        if z is None:
            messagebox.showwarning('提示', '先登录并在左栏选好「大区 / 分区」')
            return
        role = None
        for sj in slots:
            if sj.get('sel') and sj['role']:
                role = sj['role']
                break
        name = (e_role.get() or '').strip() or ((role or {}).get('name') or '')
        if not name:
            messagebox.showwarning('提示', '把「角色名」填上（或点「读角色」后点选一个）')
            return
        acct = e_acct.get().strip()
        pwd = e_pwd.get().strip()
        # ★★★ 2026-10-21 多账号录入防串号：
        #   槽位里的角色是「左栏这条录入连接登录的那个账号」读回来的。
        #   用户录完 A 账号后直接把输入框改成 B、没重新点「登 录」就来点录入，
        #   就会存出「B 账号 + A 的角色名/cid/rid」这种永远上不了线的死档案。
        #   手填角色名（槽位没数据）不拦 —— 那种情况本来就不依赖连接。
        _pc_ac = (getattr(pc, '_acct', '') or '').strip()
        if role and acct and _pc_ac and _pc_ac != acct:
            log('[!] 账号对不上：左栏登录的是「%s」，输入框是「%s」—— '
                '「%s」是上一个账号的角色，先点「登 录」重新读一次再选'
                % (_pc_ac, acct, role.get('name') or '?'))
            messagebox.showwarning(
                '账号对不上',
                '左栏当前登录的账号是「%s」，\n'
                '而输入框里写的是「%s」。\n\n'
                '下面选中的角色「%s」是「%s」名下的，\n'
                '存进去这条档案上线时会匹配不到角色。\n\n'
                '请先点「登 录」用「%s」重新读一次角色。'
                % (_pc_ac, acct, role.get('name') or '?', _pc_ac, acct))
            return
        #   左栏线路框里如果用户手填了名字，就按手填的存（编辑档案也能改）。
        line_name = (cb_line.get() or '').strip()
        row = {'key': arch_key(acct, z['name'], name),
               'acct': acct, 'pwd': pwd,
               'area': selected_area_name(), 'zone': z['name'],
               'line': line_name, 'name': name,
               'cid': (role or {}).get('cid') or 0,
               'rid': (role or {}).get('id') or 0,
               'cls': '', 't': time.time()}
        for k, r in enumerate(ARCH):
            if r.get('key') == row['key']:
                ARCH[k] = row          # 同角色重新录入 = 更新密码/线路
                break
        else:
            ARCH.append(row)
        save_arch(ARCH)
        render_arch()
        select_arch_key(row['key'])
        log('[*] 已录入「%s」：%s / %s / %s —— 在中间列表选中它，右侧点「上线」'
            % (name, acct, z['name'], line_name or '默认线路'))
        # ★★★ 2026-10-21 定案（12:40 探针实证）：录入完了**连接不断开**，
        #   收进闲置池（park_probe）留给同账号下次直接用。
        #   服务端对同一账号的 World 会话释放极慢：断开后 25 秒内重连，
        #   服务端连 0x20C 都不回 —— 录完就断 = 同账号第二个角色必卡死。
        #   老版本 v3.0 一直是"不断连接"，这就是它"登录都正常"的真正原因。
        cl = PROBE.get('cur')
        PROBE['cur'] = None
        park_probe(cl)
        reset_probe_ui()
        for sj in slots:
            sj['role'] = None
            sj['sel'] = False
        try:
            e_role.delete(0, 'end')
        except Exception:
            pass
        repaint_slots()
        log('   （录入完成，连接已保留在闲置池 —— 同账号接着录下一个角色不用重新登录；'
            '换账号直接填账号密码点「登 录」）')

    # ---- 上线 / 下线
    def online_one(row, quiet=False):
        if not row:
            return
        if not (row.get('acct') and row.get('pwd')):
            log('[!] 「%s」档案里没有账号密码，请重新录入' % row.get('name'))
            return
        s = SESS.get(row['key'])
        _ac = (row.get('acct') or '').strip()

        # ★★★ 2026-10-21 关键：**直接用录入连接上线，零重连**。
        #   服务端对同一账号的 World 会话释放极慢（12:40 探针：断开 25 秒后重连，
        #   服务端连 0x20C 都不回，15 秒超时）—— 所以"回收录入连接再重新登录进世界"
        #   这条路基本必失败，不能走。
        #   而录入连接此刻**已经登录好、World 也连着、角色列表正好是这批角色**，
        #   直接把它接管成这个角色的会话连接，只发「选角 + 进世界」就行。
        #   这也正是老版本 v3.0「一条连接从录入走到上线」的做法。
        if s is None:
            _p = None
            _c = PROBE.get('cur')
            if _c is not None and (getattr(_c, '_acct', '') or '').strip() == _ac:
                _p = _c
                PROBE['cur'] = None
            if _p is None:
                _p = unpark_probe(_ac)
            if _p is not None:
                _ln = _match_zone({'arch': row}, _p.lines)
                if (_ln is not None and _p.ls is not None and _p.roles
                        and _p.state in ('roles', 'world')):
                    s = new_session(row, cl=_p)
                    s['state'] = 'world'
                    s['wline'] = _ln.get('name') or ''
                    s['login_t'] = time.time()
                    _p.tag = row.get('name') or ''
                    _p.rhythm = False
                    log('[*] 「%s」直接用录入连接进游戏（不重连，避开服务端冷却）'
                        % (row.get('name') or '?'))
                    _p.post('enter', line=_ln,
                            role_name=row.get('name'),
                            wline_name=(row.get('line') or None))
                    render_arch()
                    if row.get('key') == CUR['key']:
                        apply_cur()
                    return
                # 这条连接用不上（没读角色 / 没有分区）→ 回收，走正常流程
                log('[*] 录入连接里没有可用的角色列表 —— 回收它，重新登录上线…')
                retire_probe(_p)
                root.after(4000,
                           safe(lambda r=row, q=quiet: online_one(r, q), '延迟上线'))
                return
            s = new_session(row)
        _st = s.get('state') or 'offline'
        if _st in ('online', 'login', 'world', 'entering'):
            if not quiet:
                log('[*] 「%s」已经在%s了' % (row.get('name'),
                                            '线' if _st == 'online' else '上线中'))
            return
        # ★ 服务端限制：同一个账号只允许 1 个角色在线。
        #   多开靠的是**不同账号**；同账号两个角色同时上线会互相顶掉，
        #   所以这里先拦下来讲清楚，别让用户看到两个都"在线中"又互相掉线。
        for _k, _o in SESS.items():
            if _k == row['key'] or not _ac:
                continue
            if ((_o.get('arch') or {}).get('acct') or '').strip() == _ac \
                    and (_o.get('state') or '') in ('online', 'login',
                                                    'world', 'entering'):
                log('[!] 账号「%s」已经有一个角色在线 —— 服务端同账号只允许 1 个，'
                    '先把「%s」下线再上「%s」'
                    % (_ac, (_o.get('arch') or {}).get('name') or '?',
                       row.get('name') or '?'))
                if not quiet:
                    messagebox.showwarning(
                        '同账号限制',
                        '账号「%s」已经有一个角色在线（%s）。\n'
                        '服务端同一账号只允许 1 个角色在线，\n'
                        '多开请用不同账号的角色。'
                        % (_ac, (_o.get('arch') or {}).get('name') or '?'))
                return
        # 走到这里说明这个角色**已经有会话**（之前上过线 / 上次失败过），
        # 不能再接管录入连接了，但那个账号的录入连接还挂着的话必须先让开，
        # 否则新开的 World 一定被服务端顶掉。
        _hold = None
        _c = PROBE.get('cur')
        if _c is not None and (getattr(_c, '_acct', '') or '').strip() == _ac:
            _hold = _c
            PROBE['cur'] = None
        else:
            _hold = unpark_probe(_ac)
        if _hold is not None:
            log('[*] 账号「%s」的录入连接还占着 —— 先回收它，8 秒后开始上线…' % _ac)
            retire_probe(_hold)
            root.after(8000,
                       safe(lambda r=row, q=quiet: online_one(r, q), '延迟上线'))
            return

        s['arch'] = row
        s['state'] = 'login'
        s['msg'] = ''
        s['login_t'] = time.time()
        s['ev'] = s['ev'] or queue.Queue()
        s['cl'].tag = row.get('name') or ''
        log('[*] 正在上线「%s」（%s / %s）…'
            % (row.get('name'), row.get('acct'), row.get('zone')))
        s['cl'].post('login', host=LOGIN_HOST_DEF, port=LOGIN_PORT_DEF,
                     acct=row.get('acct') or '', pwd=row.get('pwd') or '')
        render_arch()
        if row.get('key') == CUR['key']:
            apply_cur()

    def offline_one(row, quiet=False):
        s = SESS.get(row.get('key')) if row else None
        if not s or not s.get('cl'):
            return
        try:
            s['cl'].post('logout')
        except Exception:
            pass
        if not quiet:
            log('[*] 正在下线「%s」…' % (row.get('name') or ''))

    def on_online_btn():
        row = row_by_key(CUR['key'])
        if not row:
            messagebox.showwarning('提示', '先在中间列表里选一个角色')
            return
        s = SESS.get(CUR['key']) or {}
        if (s.get('state') or 'offline') == 'online':
            offline_one(row)
        else:
            online_one(row)

    def on_all_on():
        if not ARCH:
            messagebox.showwarning('提示', '还没有录入任何角色')
            return
        # ★ 错开 0.8 秒一个个上：同时打登录服容易被判成异常，
        #   而且每个角色本来要走「登录→读分区→进世界」三步。
        for _i, _r in enumerate(list(ARCH)):
            root.after(_i * 800,
                       safe(lambda r=_r: online_one(r, quiet=True), '全部上线'))
        log('[*] 已排入全部上线（%d 个角色，各自独立连接，间隔 0.8 秒）'
            % len(ARCH))

    def on_all_off():
        for r in ARCH:
            offline_one(r, quiet=True)
        log('[*] 已请求全部下线')

    def on_redit():
        row = row_by_key(CUR['key'])
        if not row:
            messagebox.showwarning('提示', '先选一个角色')
            return
        dlg = tk.Toplevel(root)
        dlg.title('编辑角色 —— %s' % (row.get('name') or ''))
        dlg.transient(root)
        dlg.configure(bg=BG)
        dlg.resizable(False, False)
        fr = tk.Frame(dlg, bg=BG)
        fr.pack(padx=12, pady=10)
        fr.columnconfigure(1, weight=1)
        ents = {}
        fields = (('acct', '账号'), ('pwd', '密码'), ('area', '区服'),
                  ('zone', '分区'), ('line', '线路'), ('name', '角色名'))
        for i, (k, lab) in enumerate(fields):
            tk.Label(fr, text=lab, bg=BG, fg=FG, font=F(10)).grid(
                row=i, column=0, sticky='w', pady=4)
            e = tk.Entry(fr, font=F(10), width=22,
                         show=('*' if k == 'pwd' else ''))
            e.insert(0, str(row.get(k) or ''))
            e.grid(row=i, column=1, sticky='we', pady=4, padx=(8, 0))
            ents[k] = e

        def _ok():
            old = row.get('key')
            for k, e in ents.items():
                row[k] = e.get().strip()
            row['key'] = arch_key(row.get('acct'), row.get('zone'),
                                  row.get('name'))
            if old != row['key'] and old in SESS:
                SESS[row['key']] = SESS.pop(old)
                if CUR['key'] == old:
                    CUR['key'] = row['key']
            save_arch(ARCH)
            render_arch()
            apply_cur()
            log('[*] 已保存「%s」的档案' % row.get('name'))
            dlg.destroy()

        bb = tk.Frame(dlg, bg=BG)
        bb.pack(fill='x', padx=12, pady=(0, 10))
        ttk.Button(bb, text='保存', command=safe(_ok, '保存档案')).pack(side='right')
        ttk.Button(bb, text='取消', command=dlg.destroy).pack(side='right', padx=(0, 6))
        dlg.protocol('WM_DELETE_WINDOW', dlg.destroy)

    def on_rdel():
        row = row_by_key(CUR['key'])
        if not row:
            messagebox.showwarning('提示', '先选一个角色')
            return
        if not messagebox.askyesno('删除角色',
                                   '从列表里删除「%s」？\n（只删本地档案，不动游戏角色）'
                                   % row.get('name')):
            return
        offline_one(row, quiet=True)
        ARCH[:] = [r for r in ARCH if r.get('key') != row.get('key')]
        SESS.pop(row.get('key'), None)
        save_arch(ARCH)
        CUR['key'] = ARCH[0]['key'] if ARCH else None
        render_arch()
        apply_cur()
        log('[*] 已删除档案「%s」' % row.get('name'))
    # ---- 传送到位（0x407）
    def on_goto():
        if not client.in_world:
            messagebox.showwarning('提示', '先让这个角色上线，进世界后才能传送')
            return
        try:
            gx = float(e_gx.get().strip())
            gy = float(e_gy.get().strip())
            gz = float(e_gz.get().strip() or 0)
        except ValueError:
            messagebox.showwarning('提示', 'X / Y / Z 必须是数字')
            return
        if not (0 < gx < 20000 and 0 < gy < 20000):
            messagebox.showwarning('提示', '坐标超出合理范围（0 ~ 20000）')
            return
        lb_tp.configure(text='发送中…', fg=WARN)
        client.post('goto', x=gx, y=gy, z=gz)

    btn_goto.configure(command=safe(on_goto, '传送到位'))

    # ---- 打怪面板（0x408）：新版技能格子
    auto_state = {'on': False}

    # ================= 技能格子逻辑（2026-10-20 新版界面）=================
    def _bindable():
        """可添加进格子的技能列表：已学 ∪ 通用，排除已在格子里的。
        返回 [(sid, 显示文本, tags)]"""
        used = set(x['sid'] for x in slots_atk) | set(x['sid'] for x in slots_buf)
        _row = row_by_key(CUR['key']) or {}
        # ★ 在线用实时下发的；没上线就用档案里上次记下的已学列表
        ids = (set(client.learned or ()) | set(_row.get('learned') or [])
               | set(COMMON_SKILLS))
        out = []
        for sid in sorted(ids):
            if not sid or sid in used:
                continue
            cfg = skill_cfg(sid) or {}
            nm = (cfg.get('name') or '').strip() or ('技能%d' % sid)
            tags = []
            if cast_profile(sid)[0]:
                tags.append('自我施法')
            _pq = prereq_of(sid)
            if _pq:
                tags.append('需:%s' % _pq[1])
            if cfg.get('nosel'):
                tags.append('无需目标')
            if cfg.get('rng'):
                tags.append('%gm' % (cfg['rng'] / 100.0))
            out.append((sid, nm, tags))
        return out

    def _sel_combo():
        """当前选中的攻击格 → 连招序列 [(sid, 组, step), ...]（按格子顺序）"""
        out = []
        for w in slots_atk:
            if w['sid'] and w['idx'] in slot_sel:
                _sc, _stp, _grp = cast_profile(w['sid'])
                out.append((w['sid'], _grp, _stp))
        return out

    def _sync_auto():
        """打怪途中改选中 = 热切换：把新连招推给客户端，不用停下再开"""
        if not auto_state['on']:
            return
        _cb = _sel_combo()
        if _cb:
            client.post('auto', on=True, combo=_cb)
            lb_atk.configure(text='自动打怪中 → 选中 %d 个技能轮流放'
                             % len(_cb), fg=GRN)
        else:
            # 全取消选中 = 没得放了，直接停
            auto_state['on'] = False
            btn_go.configure(text='开始')
            client.post('auto', on=False)
            lb_atk.configure(text='已取消全部选中，自动打怪停止', fg=MUT)

    def _slot_store():
        """格子绑定写盘 —— ★ 按当前选中角色分开存（选中状态不落盘）"""
        a = [w['sid'] for w in slots_atk]
        b = [w['sid'] for w in slots_buf]
        save_slots(a, b, CUR['key'])

    def _slot_paint(w):
        """按技能/冷却/选中状态重画一个格子（选中 = 绿框，冷却 = 灰图 + 秒数）"""
        sid = w['sid']
        lb_i = w['icon']
        # 把状态挂在控件上，方便自测脚本和排障时直接读（不占内存，也不影响渲染）
        w['frame']._sid, w['frame']._sel = sid, bool(w.get('sel', False))
        if not sid:
            img, _has = _slot_photo(0, False, False)
            lb_i.configure(image=img, text='＋ 添加', fg=MUT, bg=PANEL)
            w['cd'].configure(text='')
            w['cd'].place_forget()
            w['cd_on'] = False
            return
        cfg = skill_cfg(sid) or {}
        nm = (cfg.get('name') or '').strip() or ('技能%d' % sid)
        left = 0.0
        if client.in_world:
            left = max(0.0, client.skill_cd.get(sid, 0.0) - time.time())
            left = max(left, client.grp_cd - time.time())
        img, has = _slot_photo(sid, left > 0, w.get('sel', False))
        lb_i.configure(image=img, bg=PANEL)
        if has:
            # ★ 用户要求（2026-10-20）：有图标就**图标占满整个格子、不显示汉字**，
            #   技能名改由鼠标悬停的小提示条显示（见 _slot_tip_show）
            lb_i.configure(text='')
        else:
            lb_i.configure(text='%s\n%d' % (nm, sid),
                           fg=MUT if left > 0 else FG)
        # 秒数角标：只有冷却中才显示（空 Label 也会涂底色，不能一直挂着）
        on_now = left >= 1.0
        if on_now != w.get('cd_on'):
            w['cd_on'] = on_now
            if on_now:
                w['cd'].configure(text='%.0fs' % left)
                w['cd'].place(relx=1.0, rely=1.0, x=-1, y=-1)
            else:
                w['cd'].configure(text='')
                w['cd'].place_forget()
        elif on_now:
            w['cd'].configure(text='%.0fs' % left)

    def _slot_paint_all():
        for w in slots_atk:
            w['sel'] = (w['idx'] in slot_sel and w['sid'] > 0)
            _slot_paint(w)
        for w in slots_buf:
            _slot_paint(w)

    def _slot_click(kind, idx):
        w = (slots_atk if kind == 'atk' else slots_buf)[idx]
        if not w['sid']:
            _slot_add(kind, idx)             # 空框 → 添加
            return
        if kind == 'atk':
            # ★ 多选：点一下选中，再点一下取消（2026-10-20 用户要求）
            sid = w['sid']
            nm = (skill_cfg(sid) or {}).get('name') or ('技能%d' % sid)
            if idx in slot_sel:
                slot_sel.discard(idx)
                log('   已取消选中：%s(%d)' % (nm, sid))
            else:
                slot_sel.add(idx)
                log('   已选中：%s(%d)（当前共 %d 个，按格子顺序轮流放）'
                    % (nm, sid, len(slot_sel)))
            _slot_paint_all()
            if auto_state['on']:
                _sync_auto()                  # 热切换
            elif slot_sel:
                lb_atk.configure(text='已选中 %d 个技能，点「开始」按顺序轮流打'
                                 % len(slot_sel), fg=FG)
            else:
                lb_atk.configure(text='未选中技能', fg=MUT)
        else:
            # 通用格：点一下 = 立刻手动放一次（纯手动，不自动循环）
            client.post('use', skill=w['sid'])

    def _slot_menu(kind, idx):
        w = (slots_atk if kind == 'atk' else slots_buf)[idx]
        if not w['sid']:
            return
        m = tk.Menu(root, tearoff=0)
        cfg = skill_cfg(w['sid']) or {}
        m.add_command(label='清空这个格子',
                      command=lambda: _slot_clear(kind, idx))
        m.add_command(label='更换技能…',
                      command=lambda: _slot_add(kind, idx))
        try:
            m.tk_popup(root.winfo_pointerx(), root.winfo_pointery())
        finally:
            m.grab_release()

    def _slot_clear(kind, idx):
        w = (slots_atk if kind == 'atk' else slots_buf)[idx]
        w['sid'] = 0
        if kind == 'atk':
            slot_sel.discard(idx)        # ★ 清空格子也得把绿框一起去掉
        _slot_store()
        _slot_paint_all()
        log('   技能格已清空（%s #%d）' % (kind, idx + 1))

    def _slot_add(kind, idx):
        """空框/更换 → 弹已学技能列表，选中即绑定到该格"""
        items = _bindable()
        if not items:
            messagebox.showinfo('提示', '没有可添加的技能（先让角色学会技能，'
                                        '或格子已经占满）')
            return
        dlg = tk.Toplevel(root)
        dlg.title('添加技能到格子 #%d' % (idx + 1))
        dlg.transient(root)
        dlg.configure(bg=BG)
        dlg.resizable(False, False)
        tk.Label(dlg, text='选择技能（来自角色已学 + 通用）：', bg=BG, fg=FG,
                 font=F(10)).pack(anchor='w', padx=10, pady=(10, 4))
        e_f = tk.Entry(dlg, font=F(10))
        e_f.pack(fill='x', padx=10)
        lb = tk.Listbox(dlg, font=F(10), width=44, height=12)
        sb = ttk.Scrollbar(dlg, command=lb.yview)
        lb.configure(yscrollcommand=sb.set)
        lb.pack(side='left', fill='both', expand=True, padx=(10, 0),
                pady=6)
        sb.pack(side='right', fill='y', padx=(0, 10), pady=6)
        shown = []

        def _fill(kw=''):
            lb.delete(0, 'end')
            del shown[:]
            kw = (kw or '').strip()
            for sid, nm, tags in items:
                txt = '%d · %s%s' % (sid, nm,
                                     ('（%s）' % '/'.join(tags)) if tags else '')
                if kw and kw not in txt:
                    continue
                shown.append(sid)
                lb.insert('end', txt)

        def _ok(_ev=None):
            cur = lb.curselection()
            if not cur:
                return
            sid = shown[cur[0]]
            (slots_atk if kind == 'atk' else slots_buf)[idx]['sid'] = sid
            _slot_store()
            if kind == 'atk':
                slot_sel.add(idx)            # 新加的格子直接进入选中
                if auto_state['on']:
                    _sync_auto()
            _slot_paint_all()
            log('   技能格 #%d 已绑定 %d %s'
                % (idx + 1, sid, (skill_cfg(sid) or {}).get('name') or ''))
            dlg.destroy()

        _fill()
        e_f.bind('<KeyRelease>', lambda e: _fill(e_f.get()))
        lb.bind('<Double-Button-1>', _ok)
        bb = tk.Frame(dlg, bg=BG)
        bb.pack(fill='x', padx=10, pady=(0, 10))
        ttk.Button(bb, text='确定', command=_ok).pack(side='right')
        ttk.Button(bb, text='取消',
                   command=dlg.destroy).pack(side='right', padx=(0, 6))
        e_f.focus_set()
        dlg.protocol('WM_DELETE_WINDOW', dlg.destroy)

    # —— 开始 / 复活 ----
    def on_go():
        row = row_by_key(CUR['key'])
        if not row:
            messagebox.showwarning('提示', '先在中间列表里选一个角色')
            return
        if not client.in_world:
            messagebox.showwarning('提示', '「%s」还没上线 —— 先在右侧点「上 线」'
                                   % (row.get('name') or ''))
            return
        if not auto_state['on']:
            _cb = _sel_combo()
            if not _cb:
                messagebox.showwarning(
                    '提示', '先在技能格里添加并选中技能\n'
                           '（点空的格子添加，点填好的格子选中，可多选）')
                return
            auto_state['on'] = True
            try:
                sess()['auto'] = True
            except Exception:
                pass
            btn_go.configure(text='停止')
            client.post('auto', on=True, combo=_cb)
            _names = ' → '.join(
                '%s(%d)' % ((skill_cfg(c[0]) or {}).get('name') or '?', c[0])
                for c in _cb)
            log('   [自动] 开始打怪 —— %d 个技能按顺序轮流：%s'
                % (len(_cb), _names))
            lb_atk.configure(text='自动打怪中（%d 个技能轮流）' % len(_cb),
                             fg=GRN)
        else:
            auto_state['on'] = False
            try:
                sess()['auto'] = False
            except Exception:
                pass
            btn_go.configure(text='开始')
            client.post('auto', on=False)
            log('   [自动] 已停止')

    def on_relive():
        if not client.in_world:
            messagebox.showwarning('提示', '先让这个角色上线')
            return
        client.post('relive')
        lb_atk.configure(text='正在尝试复活…', fg=WARN)

    def on_team_toggle():
        """自动同意组队开关

        ★ 2026-10-21：只对**当前选中的那个角色**生效（client 是 _CurProxy），
          多开时每个角色有自己的 Client，各自独立开关。
          角色还没上线时 post 会返回 False（落到 _Offline 占位），这时只把
          意图存进会话，等 'online' 事件到了再补 post 一次。
        """
        _on = bool(var_team.get())
        _s = sess()
        try:
            _s['team'] = _on
        except Exception:
            pass
        _ok = False
        try:
            _ok = bool(client.post('team', on=_on))
        except Exception as _ex:
            log('[!] 自动同意组队设置失败：%s' % _ex)
            return
        if _ok:
            log('   [组队] %s 自动同意组队'
                % ('已开启' if _on else '已关闭'))
        else:
            log('   [组队] %s「自动同意组队」—— 该角色没上线，上线后自动套用'
                % ('已开启' if _on else '已关闭'))

    def _heal_pct_val():
        """下拉里的「30%」→ 30（非法值一律回落 30）"""
        try:
            return max(1, min(99, int(str(var_heal_pct.get())
                                     .replace('%', '').strip() or 30)))
        except (TypeError, ValueError):
            return 30

    def on_heal_toggle():
        """低血蓝自动凝神术开关

        和「自动同意组队」一个套路：只对**当前选中角色**生效（client 是
        _CurProxy）。角色没上线时 post 到不了 Client（落到离线占位），
        所以先把意图存进会话，等 'online' 事件到了再补一次。
        """
        _on = bool(var_heal.get())
        _pct = _heal_pct_val()
        var_heal_pct.set('%d%%' % _pct)
        _s = sess()
        try:
            _s['heal'] = _on
            _s['heal_pct'] = _pct
        except Exception:
            pass
        _live = (_s.get('state') == 'online') and (_s.get('cl') is not None)
        if _live:
            try:
                client.post('heal', on=_on, pct=_pct)
            except Exception as _ex:
                log('[!] 低血蓝自动凝神术设置失败：%s' % _ex)
                return
            log('   [自动] %s 低血蓝自动凝神术（阈值 %d%%）'
                % ('已开启' if _on else '已关闭', _pct))
        else:
            log('   [自动] %s 低血蓝自动凝神术 —— 该角色没上线，上线后自动套用'
                % ('已开启' if _on else '已关闭'))

    def on_heal_pct(_ev=None):
        """只改阈值：勾着的话立刻把新阈值推下去，不用重新勾一次"""
        _pct = _heal_pct_val()
        var_heal_pct.set('%d%%' % _pct)
        _s = sess()
        try:
            _s['heal_pct'] = _pct
        except Exception:
            pass
        if var_heal.get() and _s.get('state') == 'online':
            try:
                client.post('heal', on=True, pct=_pct)
            except Exception:
                pass
        log('   [自动] 凝神术阈值 = %d%%' % _pct)

    btn_go.configure(command=safe(on_go, '开始/停止'))
    btn_relive.configure(command=safe(on_relive, '复活'))
    ck_team.configure(command=safe(on_team_toggle, '自动同意组队'))
    ck_heal.configure(command=safe(on_heal_toggle, '低血蓝自动凝神术'))
    cb_heal.bind('<<ComboboxSelected>>', lambda _e: safe(on_heal_pct,
                                                         '凝神术阈值')())
    def on_radius(_ev=None):
        try:
            r = float(e_rng.get().strip() or RADIUS)
        except Exception:
            r = RADIUS
        r = max(1.0, min(500.0, r))
        e_rng.delete(0, 'end')
        e_rng.insert(0, str(int(r)))
        client.post('radius', r=r)

    e_rng.bind('<Return>', on_radius)
    e_rng.bind('<FocusOut>', on_radius)

    def on_refresh():
        client.post('refresh')
        log('   → 点了刷新：正在重新拉取周围实体…')

    btn_ref.configure(command=safe(on_refresh, '刷新怪物'))

    def on_show_npc():
        client.post('show_npc', on=bool(show_npc_var.get()))

    def on_dump():
        client.post('dump', on=bool(dump_var.get()))

    cb_npc.configure(command=safe(on_show_npc, '含NPC'))
    cb_dump.configure(command=safe(on_dump, '记收包'))

    _slot_paint_all()

    bl = load_blacklist()      # 打了叉的怪（按名字存，刷新出来也不打）

    def _bl_key(nm, eid):
        """排除名单的键：有名字按名字，没名字（未知）只能按实体ID"""
        n = (nm or '').strip()
        if n and n != '未知':
            return n
        return '0x%08x' % int(eid)

    last_npcs = []

    def _draw_npcs(lst):
        last_npcs[:] = list(lst or [])
        keep = tv_npc.selection()
        keepid = keep[0] if keep else None
        seen = set()
        # ★ 按传入顺序（已经是距离升序）把行「移动」到对应位置。
        #   ⚠ 以前只 item(...) 改数值、从不 move，新怪 append 到末尾，
        #     老怪永远停在第一次出现的位置 —— 所以排序逻辑是对的，
        #     界面上却完全看不出顺序。这就是「距离排序没有」的根因。
        for idx, (d, nm, eid, hp, hpmax, kind, lvl) in enumerate(lst):
            iid = str(eid)
            seen.add(iid)
            if hp is None:
                hps = '—'
            elif hpmax:
                hps = '%d/%d' % (hp, hpmax)
            else:
                hps = str(hp)
            # 排除列：打了叉的显示 ✗（还在列表里，方便再点一下取消）
            vals = ('✗' if _bl_key(nm, eid) in bl else '□', nm, kind, lvl or '—',
                    ('%.1f m' % d) if d >= 0 else '距离?', hps, '0x%08x' % eid)
            if tv_npc.exists(iid):
                tv_npc.item(iid, values=vals)
            else:
                tv_npc.insert('', 'end', iid=iid, values=vals)
            tv_npc.move(iid, '', idx)
        for iid in tv_npc.get_children():
            if iid not in seen:
                tv_npc.delete(iid)
        if keepid and tv_npc.exists(keepid):
            tv_npc.selection_set(keepid)
            tv_npc.see(keepid)

    def on_npc_click(ev):
        """★ 点第一列那个小方框 = 排除 / 取消排除这只怪（按名字）

        打了 ✗ 的怪：不打它，而且**刷新出来（新的实体ID、同一个名字）也不打**。
        排除后它还留在列表里，方便再点一下取消 —— 名字存进 怪物黑名单.json。
        """
        if tv_npc.identify_column(ev.x) != '#1':
            return                      # 只有「排除」这一列管用，别的照旧
        iid = tv_npc.identify_row(ev.y)
        if not iid:
            return
        vals = tv_npc.item(iid, 'values')
        nm = (vals[1] if len(vals) > 1 else '').strip()
        key = _bl_key(nm, iid)          # 没名字的按实体ID排除
        if key in bl:
            bl.discard(key)
            log('   ○ 「%s」取消排除，恢复打它' % key)
        else:
            bl.add(key)
            log('   ✗ 已排除「%s」—— 刷新出来也不打' % key)
        save_blacklist(bl)
        client.post('blacklist', names=sorted(bl))
        _draw_npcs(last_npcs)

    tv_npc.bind('<Button-1>', safe(on_npc_click, '怪物排除'))

    def on_quit():
        """退出：把所有在线角色的连接、以及所有录入连接都断掉，再关窗"""
        for r in list(ARCH):
            offline_one(r, quiet=True)
        # ★ 2026-10-21 多线程录入：录入连接可能同时有多条（当前 + 闲置池 + 正在回收的），
        #   一条都不能漏，否则进程退出时 socket 还挂着，账号不会立刻释放。
        for _cl in list(PARK):
            try:
                _cl.post('quit')
            except Exception:
                pass
        del PARK[:]
        for _cl in list(PROBE.get('all') or []):
            try:
                _cl.post('quit')
            except Exception:
                pass
        try:
            pc.post('quit')
        except Exception:
            pass
        root.after(400, root.destroy)

    # 点窗口右上角 X 也走正规退出（先把所有角色的连接断干净）
    root.protocol('WM_DELETE_WINDOW', safe(on_quit, '关闭窗口'))

    def on_load_roles():
        """可选：连一次分区服务器把角色列表读出来（读不到也能手填角色名）"""
        z = selected_zone()
        if z is None:
            messagebox.showwarning('提示', '先选大区 / 分区')
            return
        if pc.ls is None:
            messagebox.showwarning('提示', '先点「登 录」')
            return
        if not net_guard():
            return
        log('[*] 正在读角色列表（会连一次分区服务器，可能要十几秒）…')
        pc.post('loadroles', line=z)

    btn_role.configure(command=safe(on_load_roles, '读角色'))
    btn_login.configure(command=safe(on_login, '登录'))
    btn_enter.configure(command=safe(on_record, '录入'))
    btn_quit.configure(command=safe(on_quit, '退出程序'))
    btn_online.configure(command=safe(on_online_btn, '上线/下线'))
    btn_all_on.configure(command=safe(on_all_on, '全部上线'))
    btn_all_off.configure(command=safe(on_all_off, '全部下线'))
    btn_redit.configure(command=safe(on_redit, '编辑角色'))
    btn_rdel.configure(command=safe(on_rdel, '删除角色'))
    cb_area.bind('<<ComboboxSelected>>', safe(on_area, '选大区'))
    cb_zone.bind('<<ComboboxSelected>>', safe(on_zone, '选分区'))
    tv.bind('<<TreeviewSelect>>', safe(on_tv_select, '选中角色'))

    def _dbl(e):
        """双击角色行 = 直接上线（单击只切换右侧信息和下方数据）"""
        iid = tv.identify_row(e.y)
        if not iid:
            return
        CUR['key'] = iid
        apply_cur()
        s = SESS.get(iid) or {}
        if (s.get('state') or 'offline') == 'online':
            return
        online_one(row_by_key(iid))

    tv.bind('<Double-1>', safe(_dbl, '双击上线'))
    for sj in slots:
        sj['sel'] = False
    repaint_slots()

    # ---- 事件泵
    def pump():
        # ★ 整段包在 try 里：任何意外都不许让刷新循环断掉（否则界面会"静默卡死"）
        # ★ 2026-10-20 拆成两段 try：技能格子刷新（冷却置灰）不许被
        #   _pump_body 的异常连坐 —— 实测过一次：假客户端少个属性就让
        #   _pump_body 抛错，结果格子再也不置灰了。真实客户端同理，
        #   某条事件处理出错不该让冷却显示停摆。
        try:
            _pump_body()
        except Exception as ex:
            log('[!] 界面刷新异常（已忽略）：%s' % ex)
        try:
            # ★ 技能格子刷新：冷却置灰 / 剩余秒数 / 选中高亮（400ms 一轮，
            #   图标有缓存，空布局也不心疼）
            _slot_paint_all()
        except Exception as ex:
            log('[!] 技能格刷新异常（已忽略）：%s' % ex)
        finally:
            root.after(400, pump)

    def _update_row(key):
        """只刷新中间列表里那一行（整表重画会闪）"""
        row = row_by_key(key)
        if not row or not tv.exists(key):
            return
        s = SESS.get(key) or {}
        cls = cls_of(s) if s.get('learned') else (row.get('cls') or '—')
        try:
            tv.item(key, values=(row.get('name') or '', row.get('acct') or '',
                                 row.get('zone') or '', cls, state_text(row)))
        except Exception:
            pass

    def _match_zone(s, lines):
        """档案里存的分区名 → 服务端这次下发的分区 dict（名字优先，退包含匹配）"""
        want = (s['arch'].get('zone') or '').strip()
        if not want:
            return None
        for ln in (lines or []):
            if (ln.get('name') or '').strip() == want:
                return ln
        for ln in (lines or []):
            if want in (ln.get('name') or ''):
                return ln
        return None

    def _drain_session(s):
        """处理某个角色连接的事件：更新它的缓存；只有它被选中时才动界面"""
        key = s['key']
        cl = s.get('cl')
        if cl is None:
            return
        cur = (key == CUR['key'])
        nm_r = s['arch'].get('name') or ''
        try:
            while True:
                item = s['ev'].get_nowait()
                kind = item[0]
                data = item[1] if len(item) > 1 else None
                if kind == 'log':
                    # 非当前角色的日志不进界面（不然多开时日志全串在一起）
                    if cur:
                        _log_ui('[%s] %s' % (time.strftime('%H:%M:%S'), data))
                elif kind in ('lines', 'areas'):
                    if kind != 'lines':
                        continue
                    # ★ 登录成功 → 按档案里的分区名匹配 → 直接进角色
                    if s.get('state') != 'login':
                        continue
                    ln = _match_zone(s, data)
                    if ln is None:
                        s['state'] = 'error'
                        s['msg'] = '没找到分区「%s」' % (s['arch'].get('zone') or '')
                        _update_row(key)
                        if cur:
                            apply_cur()
                        _log_ui('[!] 「%s」%s' % (nm_r, s['msg']))
                        continue
                    s['state'] = 'world'
                    s['wline'] = ln.get('name') or ''
                    if cur:
                        lb_tst.configure(text='连接中', fg=WARN)
                        lb_atk.configure(text='正在进入分区「%s」…' % s['wline'], fg=WARN)
                    cl.post('enter', line=ln,
                            role_name=s['arch'].get('name'),
                            wline_name=(s['arch'].get('line') or None))
                elif kind == 'pick':
                    s['state'] = 'entering'
                    _update_row(key)
                    if cur:
                        apply_cur()
                elif kind == 'online':
                    s['state'] = 'online'
                    s['msg'] = ''
                    s['online_role'] = data
                    _update_row(key)
                    if cur:
                        apply_cur()
                    _log_ui('[★] 「%s」已上线' % nm_r)
                    # ★ 2026-10-21：上线后把「自动同意组队」的勾选状态套到这条
                    #   Client 上。离线时点开关只存了界面状态（那时 Client 还没建），
                    #   所以必须在这里补一次，否则「先勾再上线」不生效。
                    if s.get('team'):
                        try:
                            s['cl'].post('team', on=True)
                        except Exception:
                            pass
                    # ★ 2026-10-21：低血蓝自动凝神术同理（离线时只存了界面意图）
                    if s.get('heal'):
                        try:
                            s['cl'].post('heal', on=True,
                                         pct=s.get('heal_pct') or 30)
                        except Exception:
                            pass
                elif kind == 'offline':
                    s['state'] = 'offline'
                    s['npcs'] = []
                    s['auto'] = False
                    s['hp'] = s['hpmax'] = s['mp'] = s['mpmax'] = None
                    s['dead'] = False
                    _update_row(key)
                    if cur:
                        apply_cur()
                elif kind == 'error':
                    s['state'] = 'error'
                    s['msg'] = str(data or '')
                    _update_row(key)
                    if cur:
                        apply_cur()
                elif kind == 'learned':
                    ids = set((data or {}).get('ids') or ())
                    if ids:
                        s['learned'] = ids
                        # ★ 存进档案：这个角色离线时也能往技能格里加它学过的技能
                        row = row_by_key(key)
                        if row is not None:
                            _cl = cls_of(s)
                            if (sorted(ids) != sorted(row.get('learned') or [])
                                    or (_cl and row.get('cls') != _cl)):
                                row['learned'] = sorted(ids)
                                if _cl and _cl != '—':
                                    row['cls'] = _cl
                                save_arch(ARCH)
                    _update_row(key)
                    if cur:
                        apply_cur()
                elif kind == 'self_hp':
                    s['hp'] = data.get('hp')
                    s['hpmax'] = data.get('max')
                    s['mp'] = data.get('mp')
                    s['mpmax'] = data.get('mp_max')
                    s['dead'] = bool(data.get('dead'))
                    if cur:
                        hp_mp_text(s)
                elif kind == 'self_lv':
                    s['lv'] = data.get('lv')
                    s['exp'] = data.get('exp')
                    s['need'] = data.get('need')
                    if cur:
                        _lv_show(data)
                elif kind == 'npcs':
                    s['npcs'] = data or []
                    if cur:
                        _draw_npcs(s['npcs'])
                        if s['npcs']:
                            _p = cl.pos
                            _ps = ('我在(%.0f,%.0f)' % (_p[0], _p[1])) if _p else '位置?'
                            lb_atk.configure(
                                text='附近 %d · %s · 发 %d 受理 %d 中 %d'
                                     % (len(s['npcs']), _ps, cl.atk_sent,
                                        cl.atk_ack, cl.atk_hit), fg=GRN)
                        else:
                            try:
                                lb_atk.configure(text=cl._empty_hint(), fg=MUT)
                            except Exception:
                                lb_atk.configure(text='附近没检测到怪', fg=MUT)
                elif kind == 'auto_res':
                    s['auto'] = bool(data.get('on'))
                    if cur:
                        auto_state['on'] = s['auto']
                        btn_go.configure(text='停止' if s['auto'] else '开始')
                elif kind == 'team_res':
                    s['team'] = bool(data.get('on'))
                    if cur:
                        try:
                            var_team.set(s['team'])
                        except Exception:
                            pass
                elif kind == 'team':
                    # 队伍成员变化（0x68E 累计 / 0x68F、0x69A 清空）
                    s['mates'] = list(data or [])
                    if cur and s['mates']:
                        lb_atk.configure(text='队伍中 %d 人' % len(s['mates']),
                                         fg=FG)
                elif kind == 'bag_box':
                    # 自动识别到的箱子（0x613 背包里筛出来的），填进 6 个格子
                    s['boxes'] = list(data or [])
                    if cur:
                        _fill_boxes(data or [])
                elif kind == 'atk_res':
                    if cur and not data.get('ok'):
                        lb_atk.configure(text='× %s' % data.get('msg', ''), fg=RED)
                elif kind == 'use_res':
                    if cur:
                        if data.get('ack'):
                            lb_atk.configure(text='✓ %s(%d) 已生效'
                                             % (data.get('name'), data.get('id')),
                                             fg=GRN)
                        elif data.get('ok'):
                            lb_atk.configure(text='已发出 %s(%d)，等服务端确认…'
                                             % (data.get('name'), data.get('id')),
                                             fg=WARN)
                        else:
                            lb_atk.configure(text='× %s' % (data.get('msg') or ''),
                                             fg=RED)
                elif kind == 'goto_res':
                    if cur:
                        if data.get('ok'):
                            _x, _y, _z = data.get('pos', (0, 0, 0))
                            lb_tp.configure(text='★ 已到位：(%.1f, %.1f)' % (_x, _y),
                                            fg=GRN)
                        else:
                            lb_tp.configure(text='× 失败：%s' % data.get('msg', ''),
                                            fg=RED)
                elif kind == 'relive_res':
                    if cur:
                        if data.get('ok'):
                            lb_atk.configure(text='★ 复活成功 —— 位置已变，重新传送一次',
                                             fg=GRN)
                        else:
                            lb_atk.configure(text='× %s' % data.get('msg', ''), fg=RED)
                elif kind == 'skill_seen':
                    # ★ 2026-10-21 修 NameError：原来这里用的 SKLIB 从未定义。
                    #   另外 load_skills() 的键是**字符串**，用 int 查会永远查不到、
                    #   每来一次事件就重写一遍文件，所以统一转成 str。
                    _sid = int(data.get('id') or 0)
                    if _sid:
                        _lib = skill_lib()
                        _k = str(_sid)
                        if _k not in _lib:
                            _cfg = skill_cfg(_sid) or {}
                            _lib[_k] = {'name': _cfg.get('name', ''),
                                        'group': _cfg.get('group', 0),
                                        'step': _cfg.get('step', 0)}
                            save_skills(_lib)
                            _log_ui('技能库新增：%d %s（来自服务端确认）'
                                    % (_sid, _cfg.get('name') or '配置表无名字'))
                elif kind == 'wlines':
                    s['wlines_cache'] = data or []
        except queue.Empty:
            pass

    def _probe_ui_ready():
        """登录这一轮结束了（成功/失败都算），把「登 录」按钮恢复可点"""
        LOGIN_UI['busy'] = False
        try:
            btn_login.configure(state='normal', text='登  录')
        except Exception:
            pass

    def _pump_probe():
        """左侧录入连接的事件。

        ★★★ 2026-10-21 多线程录入：每次登录都是一条新连接，所以这里必须
          **先快照当前连接**，并在循环里校验它还"是不是当前这条"。
          否则上一条连接迟到的 areas/roles 会盖掉新账号刚读到的东西 ——
          表现就是"换了账号，角色列表还是上一个账号的"。
        """
        try:
            probe_gc()
        except Exception:
            pass
        cl = PROBE.get('cur')
        if cl is None:
            return
        ev = cl.ev
        try:
            while True:
                item = ev.get_nowait()
                if PROBE.get('cur') is not cl:
                    break          # 连接已经换了，队列里剩的属于旧账号，丢弃
                kind = item[0]
                data = item[1] if len(item) > 1 else None
                if kind == 'log':
                    # 客户端线程已经写进日志文件了，这里只补到界面上
                    _log_ui('[%s] %s' % (time.strftime('%H:%M:%S'), data))
                elif kind == 'areas':
                    _probe_ui_ready()
                    fill_areas(data)
                elif kind == 'roles':
                    fill_probe_roles(data)
                elif kind == 'wlines':
                    del WLINE[:]
                    WLINE.extend(data or [])
                    cb_line['values'] = [w['name'] for w in WLINE]
                    if WLINE:
                        cb_line.current(0)
                        cb_line.configure(state='readonly')
                        log('[*] 线路已读取 %d 条：%s'
                            % (len(WLINE), '、'.join(w['name'] for w in WLINE)))
                        for sj in slots:
                            if sj.get('sel') and sj['role']:
                                log('[*] 「%s」线路已就绪，选一条后点「录 入」'
                                    % sj['role']['name'])
                    else:
                        cb_line.set('')
                        cb_line.configure(state='disabled')
                    if data and pending_menu[0] is not None:
                        _idx = pending_menu[0]
                        pending_menu[0] = None
                        for k, o in enumerate(slots):
                            o['sel'] = (k == _idx)
                        repaint_slots()
                        root.after(200, safe(lambda: pop_lines_menu(_idx),
                                             '弹出线路菜单'))
                elif kind == 'wline_sel':
                    if 0 <= data < len(WLINE):
                        cb_line.current(data)
                elif kind == 'offline':
                    # 录入完自动退了 / 连接断了 → 左栏复位到未登录状态
                    pending_menu[0] = None
                    reset_probe_ui()
                elif kind == 'error':
                    _probe_ui_ready()
                    fail_note()          # 计入失败刹车（见 net_guard）
                    if not ROLES:
                        for sj in slots:
                            sj['name'].configure(text='读取失败', fg=RED)
                    log('[!] %s' % data)
        except queue.Empty:
            pass

    def _probe_watchdog():
        """看门狗：当前录入连接的后台线程意外死了 → 清掉它并提示。

        ★ 2026-10-21 多线程录入：**不再自动 new_probe()**。
          自动新建会凭空多一条连接（用户没点登录却发起了一次连接），
          而且新连接里没有账号信息，只会白白消耗服务端对同 IP 的连接配额。
          现在只把死连接摘掉，用户点「登 录」时自然会新建一条干净的。
        """
        cl = PROBE.get('cur')
        if cl is None:
            return
        try:
            if cl.is_alive():
                return
            running = bool(getattr(cl, 'running', False))
        except Exception:
            return
        PROBE['cur'] = None
        _probe_ui_ready()
        if running:
            log('[!] 录入连接的后台线程意外停止了 —— 请重新点「登 录」'
                '（会新建一条连接）')

    def _pump_body():
        try:
            _probe_watchdog()
        except Exception:
            pass
        try:
            _pump_probe()
        except Exception as ex:
            log('[!] 录入连接刷新异常（已忽略）：%s' % ex)
        for _key, _s in list(SESS.items()):
            try:
                _drain_session(_s)
            except Exception as ex:
                log('[!] 「%s」刷新异常（已忽略）：%s'
                    % ((_s.get('arch') or {}).get('name') or _key, ex))

    # 调试/自测入口：把会话容器露出来（排障时能直接看每个角色的状态）
    try:
        root._jg = {'SESS': SESS, 'CUR': CUR, 'ARCH': ARCH, 'pc': pc,
                    'PROBE': PROBE, 'new_probe': new_probe,
                    'retire_probe': retire_probe, 'probe_gc': probe_gc,
                    'on_login': on_login, 'on_record': on_record,
                    'on_zone': on_zone, 'LOGIN_UI': LOGIN_UI,
                    'tv': tv, 'tv_npc': tv_npc, 'btn_online': btn_online,
                    'btn_go': btn_go, 'lb_cur': lb_cur, 'lb_tst': lb_tst,
                    'lb_hp': lb_hp, 'lb_rcls': lb_rcls, 'lb_rsk': lb_rsk,
                    'lb_atk': lb_atk, 'slots_atk': slots_atk,
                    'slots_buf': slots_buf, 'apply_cur': apply_cur,
                    'render_arch': render_arch,
                    'select_arch_key': select_arch_key,
                    'cb_area': cb_area, 'cb_zone': cb_zone,
                    'on_area': on_area, 'on_zone': on_zone,
                    'on_record': on_record, 'slots': slots,
                    'e_acct': e_acct, 'e_pwd': e_pwd,
                    'on_load_roles': on_load_roles, 'e_role': e_role,
                    'btn_role': btn_role,
                    # ★ 2026-10-21：物品格也露出来，方便自测直接喂数据
                    'slots_item': slots_item, 'fill_boxes': _fill_boxes,
                    'lb_lv': lb_lv, 'lb_exp': lb_exp}
    except Exception:
        pass

    # ---- 启动：先按已录入的档案把列表铺出来
    render_arch()
    if ARCH:
        select_arch_key(ARCH[0].get('key'))
    else:
        apply_cur()
    root.after(300, pump)
    log('用法① 录入：登录 → 选「大区信息」→ 选「分区」(自动读角色) → '
        '点选角色(读线路) → 选线路 → 点「录 入」')
    log('用法② 上线：在中间「角色列表」点一个角色 → 右侧看它信息 → 点「上 线」'
        '（双击列表行也能直接上线）')
    log('用法③ 多开：不同角色各自独立连接，可以同时在线上；「全部上线/全部下线」一键批量。')
    log('用法④ 切换：点列表里的角色，下方「职业 / 技能 / 周围怪物」全部换成它的数据。')
    log('录入完会自动断开临时连接，把账号释放出来，不然上线会被自己占着。')
    if VERIFIED or HIDDEN:
        log('技能状态已载入：可用 %d 个、已隐藏 %d 个'
            % (len(VERIFIED), len(HIDDEN - VERIFIED)))
        log('   想恢复被隐藏的技能：删掉同目录的「技能状态.json」再启动')
    log('提示：若提示账号被占用，先关掉游戏客户端 / 启动器再试。')
    return root


def main():
    load_state()                     # 读回上次探测的成果（能用/不能用的技能）
    ev = queue.Queue()
    client = Client(ev)
    client.start()
    root = build_gui(client)
    try:
        root.mainloop()
    finally:
        client.abort = True
        client.post('quit')
        time.sleep(0.4)


if __name__ == '__main__':
    main()
