[app]

# 应用显示名（手机上看到的名字）
title = 极光助手
package.name = helper
package.domain = com.jiguang

# 源码目录 = 本目录（main.py / jg_core.py / 技能图标 / 两个 txt 都在这）
source.dir = .
source.include_exts = py,png,jpg,jpeg,txt,json,otf,ttf
# ⚠ 这里故意**不写**中文 include_patterns：中文路径交给 ext 规则统一收进来，
#   免得 buildozer 解析中文 pattern 时出岔子（技能图标/*.png 会被 png 规则收走）
source.exclude_dirs = bin, .git, __pycache__, .buildozer, tests

version = 6.2

# 只依赖 kivy；协议层是纯标准库（socket/struct/threading/queue/json）
requirements = python3,kivy

orientation = portrait
fullscreen = 0

# 联网 + 后台保活（挂机必须）
android.permissions = INTERNET,ACCESS_NETWORK_STATE,WAKE_LOCK,FOREGROUND_SERVICE

# 目标/最低 API（Android 7.0 ~ 13）
android.api = 33
android.minapi = 24
android.ndk_api = 24
android.archs = arm64-v8a,armeabi-v7a
android.accept_sdk_license = True
android.allow_backup = True

# 允许程序在后台继续跑（Android 会把没声明的后台网络掐掉）
android.enable_androidx = True
android.private_storage = True

# 包名不允许以数字开头，用 com 域反而更稳；想改就改这两行
# android.meta_data =

[buildozer]
log_level = 2
warn_on_root = 1
