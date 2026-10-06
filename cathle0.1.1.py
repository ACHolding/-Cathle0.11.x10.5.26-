#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
cathle 0.1.1 — single-file N64 emulator monolith
Engine: cathle
VR4300 opcode surface complete (integer/FPU/COP0 + RI/CU traps).
UltraHLE port: OP_PATCH/OP_GROUP, full PATCH.C table, SYM.C oscall scan,
ospatch/osignore, ultra.ini game profiles, OS/RSP/RDP/PIF HLE (Python 3.14).
HLE IPL3 boot + signature patch install for commercial titles (SM64 first; Fast3D/F3DEX2 soft RDP).

Note on ContraSF Corn: Corn's source was never released (closed-source Win32).
This tree cannot literally import Corn; SM64-first HLE + soft RDP follows the
same commercial-boot goals while keeping the cathle Tk GUI.

Single-file Python 3.14 — Tkinter, no external assets
Run: python3 cathle0.1.1.py --self-test
"""
from __future__ import annotations
import base64, math, os, platform, struct, sys, time, random
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, Callable, Any
import threading

_SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
_DEFAULT_ROM_DIR = os.path.join(_SCRIPT_DIR, "Roms")
_ROM_SCAN_MAX_FILES = 512
try:
    import tkinter as tk
    from tkinter import filedialog, messagebox, simpledialog, ttk
except ImportError:
    tk = filedialog = messagebox = simpledialog = ttk = None

APP_NAME = "cathle 0.1.1"
VERSION = "0.1.1"; ENGINE_NAME = "cathle"; PYTHON_TARGET = "3.14"
WINDOW_TITLE = "cathle 0.1.1"
ROM_EXTENSIONS = (".z64", ".v64", ".n64", ".rom", ".bin")
# cathle's classic report-view ROM browser fields.
ROM_BROWSER_COLUMNS = (
    ("good_name", "Good Name", 218),
    ("status", "Status", 92),
    ("core_notes", "Notes (Core)", 120),
    ("plugin_notes", "Notes (default plugins)", 188),
    ("force_feedback", "Force Feedback", 100),
)

CATHLE_WIN_GRAY = CATHLE_WIN_FACE = CATHLE_BTN_FACE = "#c0c0c0"
CATHLE_BTN_HIGHLIGHT = "#ffffff"; CATHLE_BTN_SHADOW = "#808080"
CATHLE_PANEL_WHITE = "#ffffff"; CATHLE_TEXT = "#000000"; CATHLE_SPLASH_GRAY = "#808080"
CATHLE_VIEWPORT_BORDER = "#808080"; CATHLE_LIST_SEL_BG = "#000080"; CATHLE_LIST_SEL_FG = "#ffffff"
BG_COLOR, PANEL_COLOR, TEXT_COLOR = CATHLE_WIN_GRAY, CATHLE_BTN_FACE, CATHLE_TEXT
ACCENT_BLUE, TERMINAL_GREEN, STATUS_RED, WHITE = CATHLE_TEXT, "#008000", "#800000", CATHLE_PANEL_WHITE
def _cathle_ui_fonts():
    if platform.system() == "Darwin": return ("Tahoma",11),("Courier New",11),("Tahoma",11,"bold")
    if platform.system() == "Windows": return ("MS Sans Serif",8),("Courier New",9),("MS Sans Serif",8,"bold")
    return ("TkDefaultFont",9),("Courier New",9),("TkDefaultFont",9,"bold")
UI_FONT, UI_FONT_MONO, UI_FONT_BOLD = _cathle_ui_fonts()

RDRAM_SIZE = 8*1024*1024; RDRAM_SIZE_4MB = 4*1024*1024
RSP_DMEM_SIZE = 0x1000; RSP_IMEM_SIZE = 0x1000; PIF_RAM_SIZE = 0x40
EEPROM_4K_SIZE = 0x200; EEPROM_16K_SIZE = 0x800; SRAM_SIZE = 0x8000; FLASHRAM_SIZE = 0x10000
MASK_8 = 0xFF; MASK_16 = 0xFFFF; MASK_32 = 0xFFFFFFFF; MASK_64 = 0xFFFFFFFFFFFFFFFF
# N64 timing — VR4300 @ 93.75 MHz, NTSC VI @ 60 Hz (PAL @ 50 Hz).
N64_CPU_HZ = 93_750_000
N64_VI_NTSC_HZ = 60
N64_VI_PAL_HZ = 50
N64_CYCLES_PER_FRAME_NTSC = N64_CPU_HZ // N64_VI_NTSC_HZ  # 1_562_500
N64_CYCLES_PER_FRAME_PAL = N64_CPU_HZ // N64_VI_PAL_HZ
# Pure-Python interpreter budget per displayed frame (~14 ms of work).
INTERP_FRAME_BUDGET_S = 0.014
INTERP_MIN_STEPS = 12_000
INTERP_MAX_STEPS = 200_000
INTERP_BOOT_STEPS = 80_000  # CORN-style SM64-first: burn CPU until first lit frame
FRAME_PERIOD_NTSC = 1.0 / N64_VI_NTSC_HZ
FRAME_PERIOD_PAL = 1.0 / N64_VI_PAL_HZ
def u8(v): return v & MASK_8
def u16(v): return v & MASK_16
def u32(v): return v & MASK_32
def u64(v): return v & MASK_64
def sign8(v): v &= MASK_8; return v - 0x100 if v & 0x80 else v
def sign16(v): v &= MASK_16; return v - 0x10000 if v & 0x8000 else v
def sign32(v): v &= MASK_32; return v - 0x100000000 if v & 0x80000000 else v
def sign64(v): v &= MASK_64; return v - 0x10000000000000000 if v & 0x8000000000000000 else v
def sx8_to_64(v): return u64(sign8(v))
def sx16_to_64(v): return u64(sign16(v))
def sx32_to_64(v): return u64(sign32(v))
def be32(data, off):
    if off < 0 or off + 3 >= len(data): return 0
    return struct.unpack_from(">I", data, off)[0]
def put_be32(data, off, val):
    if off < 0 or off + 3 >= len(data): return
    struct.pack_into(">I", data, off, val & MASK_32)
def be64(data, off):
    if off < 0 or off + 7 >= len(data): return 0
    return struct.unpack_from(">Q", data, off)[0]
def put_be64(data, off, val):
    if off < 0 or off + 7 >= len(data): return
    struct.pack_into(">Q", data, off, val & MASK_64)
def f32_to_bits(v):
    try:
        return struct.unpack(">I", struct.pack(">f", float(v)))[0]
    except (OverflowError, ValueError):
        return 0x7F800000 if float(v) > 0.0 else 0xFF800000
def bits_to_f32(v): return struct.unpack(">f", struct.pack(">I", v & MASK_32))[0]
def f64_to_bits(v):
    try:
        return struct.unpack(">Q", struct.pack(">d", float(v)))[0]
    except (OverflowError, ValueError):
        return 0x7FF0000000000000 if float(v) > 0.0 else 0xFFF0000000000000
def bits_to_f64(v): return struct.unpack(">d", struct.pack(">Q", v & MASK_64))[0]

# ── N64 hardware register map ──
SP_MEM_ADDR=0x04040000; SP_DRAM_ADDR=0x04040004; SP_RD_LEN=0x04040008; SP_WR_LEN=0x0404000C
SP_STATUS=0x04040010; SP_DMA_FULL=0x04040014; SP_DMA_BUSY=0x04040018; SP_SEMAPHORE=0x0404001C
SP_PC=0x04080000; SP_IBIST=0x04080004
SP_STATUS_HALT=0x0001; SP_STATUS_BROKE=0x0002; SP_STATUS_DMA_BUSY=0x0004; SP_STATUS_DMA_FULL=0x0008
SP_STATUS_IO_FULL=0x0010; SP_STATUS_SSTEP=0x0020; SP_STATUS_INTR_BREAK=0x0040
SP_CLR_HALT=0x0001; SP_SET_HALT=0x0002; SP_CLR_BROKE=0x0004; SP_CLR_INTR=0x0008; SP_SET_INTR=0x0010
SP_CLR_SSTEP=0x0020; SP_SET_SSTEP=0x0040; SP_CLR_INTR_BREAK=0x0080; SP_SET_INTR_BREAK=0x0100
SP_CLR_SIG0=0x0200; SP_SET_SIG0=0x0400; SP_CLR_SIG1=0x0800; SP_SET_SIG1=0x1000
SP_CLR_SIG2=0x2000; SP_SET_SIG2=0x4000; SP_CLR_SIG3=0x00010000; SP_SET_SIG3=0x00020000
SP_CLR_SIG4=0x00040000; SP_SET_SIG4=0x00080000; SP_CLR_SIG5=0x00100000; SP_SET_SIG5=0x00200000
SP_CLR_SIG6=0x00400000; SP_SET_SIG6=0x00800000; SP_CLR_SIG7=0x01000000; SP_SET_SIG7=0x02000000
DPC_START=0x04100000; DPC_END=0x04100004; DPC_CURRENT=0x04100008; DPC_STATUS=0x0410000C
DPC_CLOCK=0x04100010; DPC_BUFBUSY=0x04100014; DPC_PIPEBUSY=0x04100018; DPC_TMEM=0x0410001C
DPC_STATUS_XBUS_DMEM_DMA=0x0001; DPC_STATUS_FREEZE=0x0002; DPC_STATUS_FLUSH=0x0004
DPC_CLR_XBUS_DMEM_DMA=0x0001; DPC_SET_XBUS_DMEM_DMA=0x0002; DPC_CLR_FREEZE=0x0004; DPC_SET_FREEZE=0x0008
DPC_CLR_FLUSH=0x0010; DPC_SET_FLUSH=0x0020
DPS_TBIST=0x04200000; DPS_TEST_MODE=0x04200004; DPS_BUFTEST=0x04200008; DPS_DETAIL=0x0420000C
MI_MODE=0x04300000; MI_VERSION=0x04300004; MI_INTR=0x04300008; MI_INTR_MASK=0x0430000C
MI_MODE_INIT=0x0001; MI_MODE_EBUS=0x0002; MI_MODE_RDRAM=0x0004
MI_CLR_INIT=0x0001; MI_SET_INIT=0x0002; MI_CLR_EBUS=0x0004; MI_SET_EBUS=0x0008; MI_CLR_DP_INTR=0x0010
MI_CLR_RDRAM=0x0020; MI_SET_RDRAM=0x0040
MI_INTR_SP=0x01; MI_INTR_SI=0x02; MI_INTR_AI=0x04; MI_INTR_VI=0x08; MI_INTR_PI=0x10; MI_INTR_DP=0x20
MI_INTR_MASK_CLR_SP=0x0001; MI_INTR_MASK_SET_SP=0x0002; MI_INTR_MASK_CLR_SI=0x0004; MI_INTR_MASK_SET_SI=0x0008
MI_INTR_MASK_CLR_AI=0x0010; MI_INTR_MASK_SET_AI=0x0020; MI_INTR_MASK_CLR_VI=0x0040; MI_INTR_MASK_SET_VI=0x0080
MI_INTR_MASK_CLR_PI=0x0100; MI_INTR_MASK_SET_PI=0x0200; MI_INTR_MASK_CLR_DP=0x0400; MI_INTR_MASK_SET_DP=0x0800
VI_STATUS=0x04400000; VI_ORIGIN=0x04400004; VI_WIDTH=0x04400008; VI_INTR=0x0440000C
VI_V_CURRENT=0x04400010; VI_BURST=0x04400014; VI_V_SYNC=0x04400018; VI_H_SYNC=0x0440001C
VI_LEAP=0x04400020; VI_H_START=0x04400024; VI_V_START=0x04400028; VI_V_BURST=0x0440002C
VI_X_SCALE=0x04400030; VI_Y_SCALE=0x04400034
AI_DRAM_ADDR=0x04500000; AI_LEN=0x04500004; AI_CONTROL=0x04500008; AI_STATUS=0x0450000C
AI_DACRATE=0x04500010; AI_BITRATE=0x04500014
AI_STATUS_FIFO_FULL=0x40000000; AI_STATUS_DMA_BUSY=0x80000000
PI_DRAM_ADDR=0x04600000; PI_CART_ADDR=0x04600004; PI_RD_LEN=0x04600008; PI_WR_LEN=0x0460000C
PI_STATUS=0x04600010; PI_DOM1_LAT=0x04600014; PI_DOM1_PWD=0x04600018; PI_DOM1_PGS=0x0460001C
PI_DOM1_RLS=0x04600020; PI_DOM2_LAT=0x04600024; PI_DOM2_PWD=0x04600028; PI_DOM2_PGS=0x0460002C
PI_DOM2_RLS=0x04600030; PI_STATUS_DMA_BUSY=0x0001
RI_MODE=0x04700000; RI_CONFIG=0x04700004; RI_CURRENT_LOAD=0x04700008; RI_SELECT=0x0470000C
RI_REFRESH=0x04700010; RI_LATENCY=0x04700014; RI_RERROR=0x04700018; RI_WERROR=0x0470001C
SI_DRAM_ADDR=0x04800000; SI_PIF_ADDR_RD=0x04800004; SI_PIF_ADDR_WR=0x04800010; SI_STATUS=0x04800018
SI_STATUS_INTERRUPT=0x1000; SI_STATUS_DMA_BUSY=0x2000

CP0_INDEX=0; CP0_RANDOM=1; CP0_ENTRYLO0=2; CP0_ENTRYLO1=3; CP0_CONTEXT=4; CP0_PAGEMASK=5; CP0_WIRED=6
CP0_BADVADDR=8; CP0_COUNT=9; CP0_ENTRYHI=10; CP0_COMPARE=11; CP0_STATUS=12; CP0_CAUSE=13; CP0_EPC=14
CP0_PRID=15; CP0_CONFIG=16; CP0_LLADDR=17; CP0_ERROREPC=30
STATUS_FR=0x02000000; STATUS_IE=0x0001; STATUS_EXL=0x0002; STATUS_ERL=0x0004; STATUS_BEV=0x00400000; STATUS_CU1=0x20000000
STATUS_IM2=0x0400  # RCP / MI interrupt enable in Status
CAUSE_IP2=0x0400; CAUSE_IP7=0x8000  # timer
FCR31_COND_BIT=23
FCR31_CAUSE_INEXACT=0x01; FCR31_CAUSE_UNDERFLOW=0x02; FCR31_CAUSE_OVERFLOW=0x04; FCR31_CAUSE_DIVBYZERO=0x08; FCR31_CAUSE_INVALID=0x10

# ── N64 CIC chip detection ──
CIC_NUS_6101,CIC_NUS_6102,CIC_NUS_6103,CIC_NUS_6105,CIC_NUS_6106 = 0,1,2,3,4
CIC_NUS_5167,CIC_NUS_8303,CIC_NUS_8401,CIC_NUS_DDUS,CIC_NUS_XENO = 5,6,7,8,9
SAVE_AUTO=0; SAVE_EEPROM_4K=1; SAVE_EEPROM_16K=2; SAVE_SRAM=3; SAVE_FLASHRAM=4
REGION_NTSC=0; REGION_PAL=1

def get_cic_chip_id(rom):
    if len(rom) < 0x40: return CIC_NUS_6102
    crc1, crc2 = be32(rom,0x10), be32(rom,0x14)
    country = rom[0x3E]
    pal = 0x50 if country in (0x44,0x46,0x49,0x50,0x53,0x55,0x58,0x59) else 0x00
    if country in (0x37,0x38,0x41,0x45,0x4A) or pal:
        val = crc1 ^ crc2
        if val == 0x479F1185: return CIC_NUS_6101
        if val == 0x48C8987D: return CIC_NUS_6102
        if val == 0x185879EB: return CIC_NUS_6103
        if val == 0xECBBAB3E: return CIC_NUS_6105
        if val == 0x2E24BB3E: return CIC_NUS_6106
    return CIC_NUS_6102

def recalculate_crcs(data):
    CRC_SRC_SIZE = 0x00101000
    if len(data) < 0x1000: return 0, 0
    chip = get_cic_chip_id(data)
    seeds = {CIC_NUS_6101: 0xF8CA4DDC, CIC_NUS_6102: 0xF8CA4DDC, CIC_NUS_6103: 0xA3886759,
             CIC_NUS_6105: 0xDF26F436, CIC_NUS_6106: 0x1FEA617A}
    seed = seeds.get(chip, 0xF8CA4DDC)
    t1 = t2 = t3 = t4 = t5 = t6 = seed
    ds = len(data)
    limit = min(CRC_SRC_SIZE, ds)
    is_6105 = chip == CIC_NUS_6105
    for i in range(0x1000, limit, 4):
        d = be32(data, i) if i + 3 < ds else 0
        if (t6 + d) < t6: t4 += 1
        t6 = u32(t6 + d); t3 ^= d
        shift = d & 0x1F
        r = (d << shift) | (d >> (32 - shift)) if shift else d
        t5 = u32(t5 + r)
        if t2 > d: t2 ^= r
        else: t2 ^= t6 ^ d
        if is_6105:
            jd = be32(data, 0x0750 + (i & 0xFF)) if 0x0753 + (i & 0xFF) < ds else 0
            t1 = u32(t1 + (jd ^ d))
        else:
            t1 = u32(t1 + (t5 ^ d))
    if chip == CIC_NUS_6103: crc0 = u32((t6 ^ t4) + t3); crc1 = u32((t5 ^ t2) + t1)
    elif chip == CIC_NUS_6106: crc0 = u32((t6 * t4) + t3); crc1 = u32((t5 * t2) + t1)
    else: crc0 = u32(t6 ^ t4 ^ t3); crc1 = u32(t5 ^ t2 ^ t1)
    return crc0, crc1

Z64_MAGIC = b"\x80\x37\x12\x40"; V64_MAGIC = b"\x37\x80\x40\x12"; N64_LE_MAGIC = b"\x40\x12\x37\x80"
_CART_SIGS = (Z64_MAGIC, V64_MAGIC, N64_LE_MAGIC)

def strip_documentation_header(data):
    if len(data) < 4: return
    if data[0:4] in _CART_SIGS: return
    cap = min(len(data), 16 * 1024 * 1024)
    for off in (4096, 2048, 512):
        if off + 4 <= cap and data[off:off + 4] in _CART_SIGS:
            del data[:off]; return

def apply_cart_header_defaults(data):
    if len(data)<0x40: data.extend(b"\x00"*(0x40-len(data)))
    if data[0:4] not in _CART_SIGS or data[0:4]!=Z64_MAGIC: return
    if be32(data,0x04)==0: put_be32(data,0x04,0x00000F48)
    boot=be32(data,0x08)
    if boot==0 or boot==MASK_32: put_be32(data,0x08,0x80000400)
    if be32(data,0x0C)==0: put_be32(data,0x0C,0x0000144B)
    title=data[0x20:0x34]
    if not any(title): data[0x20:0x34]=b"Ultra 64\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"[:20].ljust(20,b"\x00")
    c1,c2=recalculate_crcs(data); put_be32(data,0x10,c1); put_be32(data,0x14,c2)

def normalize_rom_bytes(data):
    data=bytearray(data); strip_documentation_header(data)
    if len(data)<4: return data
    m=data[0:4]
    if m==V64_MAGIC:
        for i in range(0,len(data)-1,2): data[i],data[i+1]=data[i+1],data[i]
        apply_cart_header_defaults(data); return data
    if m==N64_LE_MAGIC:
        for i in range(0,len(data)-3,4):
            data[i],data[i+3]=data[i+3],data[i]; data[i+1],data[i+2]=data[i+2],data[i+1]
        apply_cart_header_defaults(data); return data
    if m==Z64_MAGIC: apply_cart_header_defaults(data); return data
    return data

def seed_pif_ram(pif, cic):
    pif[:]=b"\x00"*PIF_RAM_SIZE
    for i in range(4): pif[i*4]=0x01
    for i in range(4): pif[0x20+i*4]=pif[0x21+i*4]=pif[0x22+i*4]=pif[0x23+i*4]=0x00
    pif[0x18]=0x00; pif[0x19]=0x04
    cb = {CIC_NUS_6101:(0x00,0x06,0x3F,0x3F),CIC_NUS_6102:(0x00,0x02,0x3F,0x3F),CIC_NUS_6103:(0x00,0x02,0x78,0x3F),CIC_NUS_6105:(0x00,0x02,0x91,0x3F),CIC_NUS_6106:(0x00,0x02,0x85,0x3F)}
    if cic in cb: pif[36],pif[37],pif[38],pif[39]=cb[cic]

def get_rom_region(rom):
    if len(rom)<0x3F: return REGION_NTSC
    return REGION_PAL if rom[0x3E] in (0x44,0x46,0x49,0x50,0x53,0x55,0x58,0x59) else REGION_NTSC

def detect_save_type(rom):
    if len(rom) < 0x40: return SAVE_AUTO
    cart = rom[0x3C:0x3E].decode("ascii", "ignore").upper()
    # Commercial cart-ID → save media (UltraHLE skipped EEPROM; cathle HLE's it).
    eeprom4 = {
        "SM", "GE", "NE", "KT", "SV", "WR", "RC", "BM", "BE", "TW", "IR", "GU",
        "CL", "IC", "LB", "MW", "SI", "SQ", "TE", "TM", "VG", "VT", "WA",
    }
    eeprom16 = {"ZS", "DZ", "FU", "PG", "CZ", "DL", "DO", "JD"}
    sram = {"ZL", "TP", "YW", "NB", "MZ", "CF", "DK", "FZ", "KI", "OS", "PD", "WC", "YF"}
    flash = {"PO", "MX", "DQ", "PN", "CC", "CR", "DR", "ML", "RE", "YS"}
    if cart in flash: return SAVE_FLASHRAM
    if cart in sram: return SAVE_SRAM
    if cart in eeprom16: return SAVE_EEPROM_16K
    if cart in eeprom4: return SAVE_EEPROM_4K
    return SAVE_EEPROM_4K

class N64Header:
    __slots__=("pi_bsd_dom1_lat","pi_bsd_dom1_pwd","pi_bsd_dom1_pgs","pi_bsd_dom1_rls","clock_rate","boot_address","release","crc1","crc2","title","cart_id")
    def __init__(self,data):
        if len(data)>=0x40:
            self.pi_bsd_dom1_lat=data[0];self.pi_bsd_dom1_pwd=data[1];self.pi_bsd_dom1_pgs=data[2];self.pi_bsd_dom1_rls=data[3]
            self.clock_rate=be32(data,0x04);self.boot_address=be32(data,0x08);self.release=be32(data,0x0C)
            self.crc1=be32(data,0x10);self.crc2=be32(data,0x14)
            self.title=data[0x20:0x34].decode("ascii","ignore").strip("\x00").strip()
            self.cart_id=data[0x3C:0x3E].decode("ascii","ignore")
        else:
            self.clock_rate=0;self.boot_address=0x80000400;self.release=0;self.crc1=self.crc2=0;self.title="UNKNOWN";self.cart_id="??"

@dataclass
class TLBEntry: mask:int=0;vpn2:int=0;g:bool=False;asid:int=0;pfn0:int=0;c0:int=0;d0:bool=False;v0:bool=False;pfn1:int=0;c1:int=0;d1:bool=False;v1:bool=False

_lwl_mask=[0,0xFF,0xFFFF,0xFFFFFF];_lwl_shift=[0,8,16,24]
_lwr_mask=[0xFFFFFF00,0xFFFF0000,0xFF000000,0];_lwr_shift=[24,16,8,0]
_swl_mask=[0,0xFF000000,0xFFFF0000,0xFFFFFF00];_swl_shift=[0,8,16,24]
_swr_mask=[0x00FFFFFF,0x0000FFFF,0x000000FF,0x00000000];_swr_shift=[24,16,8,0]
_ldl_mask=[0,0xFF,0xFFFF,0xFFFFFF,0xFFFFFFFF,0xFFFFFFFFFF,0xFFFFFFFFFFFF,0xFFFFFFFFFFFFFF];_ldl_shift=[0,8,16,24,32,40,48,56]
_ldr_mask=[0xFFFFFFFFFFFFFF00,0xFFFFFFFFFFFF0000,0xFFFFFFFFFF000000,0xFFFFFFFF00000000,0xFFFFFF0000000000,0xFFFF000000000000,0xFF00000000000000,0];_ldr_shift=[56,48,40,32,24,16,8,0]
_sdl_mask=[0,0xFF00000000000000,0xFFFF000000000000,0xFFFFFF0000000000,0xFFFFFFFF00000000,0xFFFFFFFFFF000000,0xFFFFFFFFFFFF0000,0xFFFFFFFFFFFFFF00];_sdl_shift=[0,8,16,24,32,40,48,56]
_sdr_mask=[0x00FFFFFFFFFFFFFF,0x0000FFFFFFFFFFFF,0x000000FFFFFFFFFF,0x00000000FFFFFFFF,0x0000000000FFFFFF,0x000000000000FFFF,0x00000000000000FF,0x0000000000000000];_sdr_shift=[56,48,40,32,24,16,8,0]
_ID_SPECIAL=0x00000;_ID_REGIMM=0x10000;_ID_COP0_RS=0x20000;_ID_COP0_CO=0x30000;_ID_COP1_RS=0x40000;_ID_COP1_BC=0x50000;_ID_FPU=0x60000;_ID_PRIMARY=0x70000
_ID_FPU_S=0;_ID_FPU_D=1;_ID_FPU_W=2;_ID_FPU_L=3;_FPU_FMT_MAP={0x10:_ID_FPU_S,0x11:_ID_FPU_D,0x14:_ID_FPU_W,0x15:_ID_FPU_L}
_DISPATCH:List[Optional[Callable]] = [None] * ((_ID_PRIMARY | 0x3F) + 1)
_OPCODE_CACHE: Dict[int, "N64Opcode"] = {}
_OPCODE_CACHE_MAX = 8192
OP_FORMAT_R="R";OP_FORMAT_I="I";OP_FORMAT_J="J";OP_FORMAT_CP="CP";OP_FORMAT_CP0_CO="CP0_CO";OP_FORMAT_REGIMM="REGIMM";OP_FORMAT_FPU_S="FPU_S";OP_FORMAT_FPU_D="FPU_D";OP_FORMAT_FPU_W="FPU_W";OP_FORMAT_FPU_L="FPU_L";OP_FORMAT_BC="BC";OP_FORMAT_BC1="BC1";OP_FORMAT_FPU_FMT="FPU_FMT"
PRIMARY_OPS={0x00:("SPECIAL",OP_FORMAT_R),0x01:("REGIMM",OP_FORMAT_REGIMM),0x02:("J",OP_FORMAT_J),0x03:("JAL",OP_FORMAT_J),0x04:("BEQ",OP_FORMAT_I),0x05:("BNE",OP_FORMAT_I),0x06:("BLEZ",OP_FORMAT_I),0x07:("BGTZ",OP_FORMAT_I),0x08:("ADDI",OP_FORMAT_I),0x09:("ADDIU",OP_FORMAT_I),0x0A:("SLTI",OP_FORMAT_I),0x0B:("SLTIU",OP_FORMAT_I),0x0C:("ANDI",OP_FORMAT_I),0x0D:("ORI",OP_FORMAT_I),0x0E:("XORI",OP_FORMAT_I),0x0F:("LUI",OP_FORMAT_I),0x10:("COP0",OP_FORMAT_CP),0x11:("COP1",OP_FORMAT_CP),0x12:("COP2",OP_FORMAT_CP),0x13:("COP3",OP_FORMAT_CP),0x14:("BEQL",OP_FORMAT_I),0x15:("BNEL",OP_FORMAT_I),0x16:("BLEZL",OP_FORMAT_I),0x17:("BGTZL",OP_FORMAT_I),0x18:("DADDI",OP_FORMAT_I),0x19:("DADDIU",OP_FORMAT_I),0x1A:("LDL",OP_FORMAT_I),0x1B:("LDR",OP_FORMAT_I),0x1C:("PATCH",OP_FORMAT_I),0x1D:("GROUP",OP_FORMAT_I),0x1E:("RESERVED_1E",None),0x1F:("RESERVED_1F",None),0x20:("LB",OP_FORMAT_I),0x21:("LH",OP_FORMAT_I),0x22:("LWL",OP_FORMAT_I),0x23:("LW",OP_FORMAT_I),0x24:("LBU",OP_FORMAT_I),0x25:("LHU",OP_FORMAT_I),0x26:("LWR",OP_FORMAT_I),0x27:("LWU",OP_FORMAT_I),0x28:("SB",OP_FORMAT_I),0x29:("SH",OP_FORMAT_I),0x2A:("SWL",OP_FORMAT_I),0x2B:("SW",OP_FORMAT_I),0x2C:("SDL",OP_FORMAT_I),0x2D:("SDR",OP_FORMAT_I),0x2E:("SWR",OP_FORMAT_I),0x2F:("CACHE",OP_FORMAT_I),0x30:("LL",OP_FORMAT_I),0x31:("LWC1",OP_FORMAT_I),0x32:("LWC2",OP_FORMAT_I),0x33:("LWC3",OP_FORMAT_I),0x34:("LLD",OP_FORMAT_I),0x35:("LDC1",OP_FORMAT_I),0x36:("LDC2",OP_FORMAT_I),0x37:("LD",OP_FORMAT_I),0x38:("SC",OP_FORMAT_I),0x39:("SWC1",OP_FORMAT_I),0x3A:("SWC2",OP_FORMAT_I),0x3B:("SWC3",OP_FORMAT_I),0x3C:("SCD",OP_FORMAT_I),0x3D:("SDC1",OP_FORMAT_I),0x3E:("SDC2",OP_FORMAT_I),0x3F:("SD",OP_FORMAT_I)}
SPECIAL_OPS={0x00:("SLL",OP_FORMAT_R),0x01:("RESERVED_SLL_01",None),0x02:("SRL",OP_FORMAT_R),0x03:("SRA",OP_FORMAT_R),0x04:("SLLV",OP_FORMAT_R),0x05:("RESERVED_SLLV_05",None),0x06:("SRLV",OP_FORMAT_R),0x07:("SRAV",OP_FORMAT_R),0x08:("JR",OP_FORMAT_R),0x09:("JALR",OP_FORMAT_R),0x0A:("MOVZ",OP_FORMAT_R),0x0B:("MOVN",OP_FORMAT_R),0x0C:("SYSCALL",OP_FORMAT_R),0x0D:("BREAK",OP_FORMAT_R),0x0E:("RESERVED_SP_0E",None),0x0F:("SYNC",OP_FORMAT_R),0x10:("MFHI",OP_FORMAT_R),0x11:("MTHI",OP_FORMAT_R),0x12:("MFLO",OP_FORMAT_R),0x13:("MTLO",OP_FORMAT_R),0x14:("DSLLV",OP_FORMAT_R),0x15:("RESERVED_DSLLV_15",None),0x16:("DSRLV",OP_FORMAT_R),0x17:("DSRAV",OP_FORMAT_R),0x18:("MULT",OP_FORMAT_R),0x19:("MULTU",OP_FORMAT_R),0x1A:("DIV",OP_FORMAT_R),0x1B:("DIVU",OP_FORMAT_R),0x1C:("DMULT",OP_FORMAT_R),0x1D:("DMULTU",OP_FORMAT_R),0x1E:("DDIV",OP_FORMAT_R),0x1F:("DDIVU",OP_FORMAT_R),0x20:("ADD",OP_FORMAT_R),0x21:("ADDU",OP_FORMAT_R),0x22:("SUB",OP_FORMAT_R),0x23:("SUBU",OP_FORMAT_R),0x24:("AND",OP_FORMAT_R),0x25:("OR",OP_FORMAT_R),0x26:("XOR",OP_FORMAT_R),0x27:("NOR",OP_FORMAT_R),0x28:("RESERVED_SP_28",None),0x29:("RESERVED_SP_29",None),0x2A:("SLT",OP_FORMAT_R),0x2B:("SLTU",OP_FORMAT_R),0x2C:("DADD",OP_FORMAT_R),0x2D:("DADDU",OP_FORMAT_R),0x2E:("DSUB",OP_FORMAT_R),0x2F:("DSUBU",OP_FORMAT_R),0x30:("TGE",OP_FORMAT_R),0x31:("TGEU",OP_FORMAT_R),0x32:("TLT",OP_FORMAT_R),0x33:("TLTU",OP_FORMAT_R),0x34:("TEQ",OP_FORMAT_R),0x35:("RESERVED_SP_35",None),0x36:("TNE",OP_FORMAT_R),0x37:("RESERVED_SP_37",None),0x38:("DSLL",OP_FORMAT_R),0x39:("RESERVED_DSLL_39",None),0x3A:("DSRL",OP_FORMAT_R),0x3B:("DSRA",OP_FORMAT_R),0x3C:("DSLL32",OP_FORMAT_R),0x3D:("RESERVED_DSLL32_3D",None),0x3E:("DSRL32",OP_FORMAT_R),0x3F:("DSRA32",OP_FORMAT_R)}
REGIMM_OPS={0x00:("BLTZ",OP_FORMAT_I),0x01:("BGEZ",OP_FORMAT_I),0x02:("BLTZL",OP_FORMAT_I),0x03:("BGEZL",OP_FORMAT_I),0x04:("RESERVED_RI_04",None),0x05:("RESERVED_RI_05",None),0x06:("RESERVED_RI_06",None),0x07:("RESERVED_RI_07",None),0x08:("TGEI",OP_FORMAT_I),0x09:("TGEIU",OP_FORMAT_I),0x0A:("TLTI",OP_FORMAT_I),0x0B:("TLTIU",OP_FORMAT_I),0x0C:("TEQI",OP_FORMAT_I),0x0D:("RESERVED_RI_0D",None),0x0E:("TNEI",OP_FORMAT_I),0x0F:("RESERVED_RI_0F",None),0x10:("BLTZAL",OP_FORMAT_I),0x11:("BGEZAL",OP_FORMAT_I),0x12:("BLTZALL",OP_FORMAT_I),0x13:("BGEZALL",OP_FORMAT_I)}
COP0_RS={0x00:("MFC0",OP_FORMAT_CP),0x01:("DMFC0",OP_FORMAT_CP),0x02:("CFC0",OP_FORMAT_CP),0x03:("RESERVED_C0_RS_03",None),0x04:("MTC0",OP_FORMAT_CP),0x05:("DMTC0",OP_FORMAT_CP),0x06:("CTC0",OP_FORMAT_CP),0x07:("RESERVED_C0_RS_07",None),0x08:("BC0",OP_FORMAT_BC),0x09:("RESERVED_C0_RS_09",None),0x0A:("RESERVED_C0_RS_0A",None),0x0B:("RESERVED_C0_RS_0B",None),0x0C:("RESERVED_C0_RS_0C",None),0x0D:("RESERVED_C0_RS_0D",None),0x0E:("RESERVED_C0_RS_0E",None),0x0F:("RESERVED_C0_RS_0F",None),0x10:("COP0_CO",OP_FORMAT_CP0_CO)}
COP0_CO={0x00:("RESERVED_C0_CO_00",None),0x01:("TLBR",OP_FORMAT_CP0_CO),0x02:("TLBWI",OP_FORMAT_CP0_CO),0x03:("RESERVED_C0_CO_03",None),0x04:("RESERVED_C0_CO_04",None),0x05:("RESERVED_C0_CO_05",None),0x06:("TLBWR",OP_FORMAT_CP0_CO),0x07:("RESERVED_C0_CO_07",None),0x08:("TLBP",OP_FORMAT_CP0_CO),0x18:("ERET",OP_FORMAT_CP0_CO),0x20:("WAIT",OP_FORMAT_CP0_CO)}
COP1_RS={0x00:("MFC1",OP_FORMAT_CP),0x01:("DMFC1",OP_FORMAT_CP),0x02:("CFC1",OP_FORMAT_CP),0x03:("RESERVED_C1_RS_03",None),0x04:("MTC1",OP_FORMAT_CP),0x05:("DMTC1",OP_FORMAT_CP),0x06:("CTC1",OP_FORMAT_CP),0x07:("RESERVED_C1_RS_07",None),0x08:("BC1",OP_FORMAT_BC1),0x10:("S",OP_FORMAT_FPU_S),0x11:("D",OP_FORMAT_FPU_D),0x14:("W",OP_FORMAT_FPU_W),0x15:("L",OP_FORMAT_FPU_L)}
COP1_FUNCT={0x00:("ADD",OP_FORMAT_FPU_FMT),0x01:("SUB",OP_FORMAT_FPU_FMT),0x02:("MUL",OP_FORMAT_FPU_FMT),0x03:("DIV",OP_FORMAT_FPU_FMT),0x04:("SQRT",OP_FORMAT_FPU_FMT),0x05:("ABS",OP_FORMAT_FPU_FMT),0x06:("MOV",OP_FORMAT_FPU_FMT),0x07:("NEG",OP_FORMAT_FPU_FMT),0x08:("ROUND.L",OP_FORMAT_FPU_FMT),0x09:("TRUNC.L",OP_FORMAT_FPU_FMT),0x0A:("CEIL.L",OP_FORMAT_FPU_FMT),0x0B:("FLOOR.L",OP_FORMAT_FPU_FMT),0x0C:("ROUND.W",OP_FORMAT_FPU_FMT),0x0D:("TRUNC.W",OP_FORMAT_FPU_FMT),0x0E:("CEIL.W",OP_FORMAT_FPU_FMT),0x0F:("FLOOR.W",OP_FORMAT_FPU_FMT),0x15:("RECIP",OP_FORMAT_FPU_FMT),0x16:("RSQRT",OP_FORMAT_FPU_FMT),0x20:("CVT.S",OP_FORMAT_FPU_FMT),0x21:("CVT.D",OP_FORMAT_FPU_FMT),0x24:("CVT.W",OP_FORMAT_FPU_FMT),0x25:("CVT.L",OP_FORMAT_FPU_FMT),0x30:("C.F",OP_FORMAT_FPU_FMT),0x31:("C.UN",OP_FORMAT_FPU_FMT),0x32:("C.EQ",OP_FORMAT_FPU_FMT),0x33:("C.UEQ",OP_FORMAT_FPU_FMT),0x34:("C.OLT",OP_FORMAT_FPU_FMT),0x35:("C.ULT",OP_FORMAT_FPU_FMT),0x36:("C.OLE",OP_FORMAT_FPU_FMT),0x37:("C.ULE",OP_FORMAT_FPU_FMT),0x38:("C.SF",OP_FORMAT_FPU_FMT),0x39:("C.NGLE",OP_FORMAT_FPU_FMT),0x3A:("C.SEQ",OP_FORMAT_FPU_FMT),0x3B:("C.NGL",OP_FORMAT_FPU_FMT),0x3C:("C.LT",OP_FORMAT_FPU_FMT),0x3D:("C.NGE",OP_FORMAT_FPU_FMT),0x3E:("C.LE",OP_FORMAT_FPU_FMT),0x3F:("C.NGT",OP_FORMAT_FPU_FMT)}

@dataclass
class CheatCode: name:str="";code:str="";enabled:bool=True
class CheatEngine:
    def __init__(self): self.codes:List[CheatCode]=[]; self.active:List[CheatCode]=[]
    def add(self,name,code): cc=CheatCode(name=name,code=code,enabled=True); self.codes.append(cc); self.active.append(cc)
    def toggle(self,idx):
        if 0<=idx<len(self.codes): self.codes[idx].enabled=not self.codes[idx].enabled; self.active=[c for c in self.codes if c.enabled]
    def apply(self,bus,rdram):
        for cc in self.active:
            if not cc.code.strip(): continue
            try:
                parts=cc.code.strip().split()
                if len(parts)>=2 and len(parts[0])==8 and len(parts[1])==8:
                    addr=int(parts[0],16);val=int(parts[1],16);ct=(addr>>28)&0xF;aa=(addr&0x0FFFFFFF)&0x00FFFFFF
                    if ct==0 and aa<RDRAM_SIZE-3: put_be32(rdram,aa,val)
                    elif ct==1 and aa<RDRAM_SIZE-1: struct.pack_into(">H",rdram,aa,val&MASK_16)
            except: pass

# libultra EEPROM_TYPE_* returned by osEepromProbe
EEPROM_TYPE_4K = 0x8000
EEPROM_TYPE_16K = 0xC000
EEPROM_BLOCK = 8


class SaveManager:
    def __init__(self):
        self.save_type=SAVE_AUTO; self.eeprom=bytearray(EEPROM_16K_SIZE); self.sram=bytearray(SRAM_SIZE)
        self.flashram=bytearray(FLASHRAM_SIZE); self.flashram_mode=0; self.flashram_addr=0; self.dirty=False
    def reset(self):
        self.eeprom=bytearray(EEPROM_16K_SIZE); self.sram=bytearray(SRAM_SIZE); self.flashram=bytearray(FLASHRAM_SIZE)
        self.flashram_mode=0; self.flashram_addr=0
    def get_save_size(self): return {SAVE_EEPROM_4K:EEPROM_4K_SIZE,SAVE_EEPROM_16K:EEPROM_16K_SIZE,SAVE_SRAM:SRAM_SIZE,SAVE_FLASHRAM:FLASHRAM_SIZE}.get(self.save_type,0)
    def eeprom_present(self) -> bool:
        return self.save_type in (SAVE_AUTO, SAVE_EEPROM_4K, SAVE_EEPROM_16K)
    def eeprom_capacity(self) -> int:
        if self.save_type == SAVE_EEPROM_16K:
            return EEPROM_16K_SIZE
        if self.save_type in (SAVE_EEPROM_4K, SAVE_AUTO):
            return EEPROM_4K_SIZE
        return 0
    def eeprom_probe(self) -> int:
        if not self.eeprom_present():
            return 0
        return EEPROM_TYPE_16K if self.save_type == SAVE_EEPROM_16K else EEPROM_TYPE_4K
    def eeprom_read_block(self, block: int, out: bytearray, off: int = 0) -> int:
        cap = self.eeprom_capacity()
        if cap <= 0:
            return -1
        addr = int(block) * EEPROM_BLOCK
        if addr < 0 or addr + EEPROM_BLOCK > cap:
            return -1
        out[off:off + EEPROM_BLOCK] = self.eeprom[addr:addr + EEPROM_BLOCK]
        return 0
    def eeprom_write_block(self, block: int, data, off: int = 0) -> int:
        cap = self.eeprom_capacity()
        if cap <= 0:
            return -1
        addr = int(block) * EEPROM_BLOCK
        if addr < 0 or addr + EEPROM_BLOCK > cap:
            return -1
        self.eeprom[addr:addr + EEPROM_BLOCK] = bytes(data[off:off + EEPROM_BLOCK])
        self.dirty = True
        return 0
    def eeprom_long_read(self, block: int, nbytes: int, bus, vaddr: int) -> int:
        if nbytes <= 0 or (nbytes & 7):
            return -1
        nblocks = nbytes // EEPROM_BLOCK
        tmp = bytearray(EEPROM_BLOCK)
        for i in range(nblocks):
            if self.eeprom_read_block(block + i, tmp) != 0:
                return -1
            for b in range(EEPROM_BLOCK):
                bus.write_u8(u32(vaddr + i * EEPROM_BLOCK + b), tmp[b])
        return 0
    def eeprom_long_write(self, block: int, nbytes: int, bus, vaddr: int) -> int:
        if nbytes <= 0 or (nbytes & 7):
            return -1
        nblocks = nbytes // EEPROM_BLOCK
        tmp = bytearray(EEPROM_BLOCK)
        for i in range(nblocks):
            for b in range(EEPROM_BLOCK):
                tmp[b] = bus.read_u8(u32(vaddr + i * EEPROM_BLOCK + b)) & 0xFF
            if self.eeprom_write_block(block + i, tmp) != 0:
                return -1
        return 0
    def pi_read(self,ca,ln,rdram,da):
        if self.save_type==SAVE_SRAM and 0<=ca<SRAM_SIZE:
            ln=min(ln,SRAM_SIZE-ca,RDRAM_SIZE-da)
            if ln>0: rdram[da:da+ln]=self.sram[ca:ca+ln]
        elif self.save_type==SAVE_FLASHRAM and 0<=ca<FLASHRAM_SIZE:
            if self.flashram_mode==1:
                ln=min(ln,FLASHRAM_SIZE-ca,RDRAM_SIZE-da)
                if ln>0: rdram[da:da+ln]=self.flashram[ca:ca+ln]
    def pi_write(self,ca,ln,rdram,da):
        if self.save_type==SAVE_SRAM and 0<=ca<SRAM_SIZE:
            ln=min(ln,SRAM_SIZE-ca,RDRAM_SIZE-da)
            if ln>0: self.sram[ca:ca+ln]=rdram[da:da+ln]; self.dirty=True
        elif self.save_type==SAVE_FLASHRAM and 0<=ca<FLASHRAM_SIZE: self._flashram_execute(ca,ln,rdram,da)
    def _flashram_execute(self,ca,ln,rdram,da):
        if self.flashram_mode==0:
            if ln>=4:
                cmd=be32(rdram,da)
                if cmd==0xFFFFFFFF: self.flashram_mode=3
                elif (cmd&0xFF000000)==0xA5000000:
                    self.flashram_addr=(cmd&0x00FFFF)<<1
                    if cmd&0x00008000: self.flashram_mode=2
                    else: self.flashram_mode=1
        elif self.flashram_mode==1: self.pi_read(ca,ln,rdram,da)
        elif self.flashram_mode==2:
            ln=min(ln,FLASHRAM_SIZE-self.flashram_addr,RDRAM_SIZE-da)
            if ln>0: self.flashram[self.flashram_addr:self.flashram_addr+ln]=rdram[da:da+ln]; self.dirty=True
            self.flashram_mode=0
        elif self.flashram_mode==3:
            if ca==0: self.flashram=bytearray(FLASHRAM_SIZE); self.dirty=True
            self.flashram_mode=0

# RGB5551 → R/G/B expansion LUTs (built once).
_RGB555_R = bytearray((((px >> 11) & 0x1F) << 3) for px in range(65536))
_RGB555_G = bytearray((((px >> 6) & 0x1F) << 3) for px in range(65536))
_RGB555_B = bytearray((((px >> 1) & 0x1F) << 3) for px in range(65536))


def rdram_rgb5551_to_ppm(rdram, origin, width, height, scale: int = 1):
    """Convert RGB5551 RDRAM to binary PPM. ``scale`` 2 ≈ 4× faster (160×120)."""
    origin &= 0xFFFFFF
    width = 320 if width < 16 or width > 640 else int(width)
    height = 240 if height < 1 or height > 240 else min(int(height), 240)
    scale = 2 if scale >= 2 else 1
    out_w = width // scale
    out_h = height // scale
    stride = width * 2
    need = origin + stride * height
    if origin < 0 or need > len(rdram):
        return None
    hdr = f"P6\n{out_w} {out_h}\n255\n".encode("ascii")
    out = bytearray(out_w * out_h * 3)
    mv = memoryview(rdram)
    lr, lg, lb = _RGB555_R, _RGB555_G, _RGB555_B
    o = 0
    y_step = scale
    x_step = scale * 2
    for y in range(0, height, y_step):
        row = origin + y * stride
        x = 0
        while x < stride:
            px = (mv[row + x] << 8) | mv[row + x + 1]
            out[o] = lr[px]
            out[o + 1] = lg[px]
            out[o + 2] = lb[px]
            o += 3
            x += x_step
    return hdr + out


def ppm_brightness(ppm: Optional[bytes]) -> float:
    """Mean channel value of a binary PPM body (0..255)."""
    if not ppm:
        return 0.0
    # Skip P6 header (3 lines).
    p = 0
    for _ in range(3):
        n = ppm.find(b"\n", p)
        if n < 0:
            return 0.0
        p = n + 1
    body = ppm[p:]
    if not body:
        return 0.0
    return sum(body) / len(body)

def normalize_commercial_entry(addr):
    addr=u32(addr)
    if addr==0 or addr==MASK_32: return 0x80000400
    hi=addr>>24
    if hi in (0x80,0xA0,0xB0):
        if hi==0xB0: return 0x80000000|(addr&0x1FFFFFFF)
        return addr
    if addr<RDRAM_SIZE: return 0x80000000|addr
    if hi==0 and addr<0x04000000: return 0x80000000|addr
    return addr

def default_rom_directory():
    try: os.makedirs(_DEFAULT_ROM_DIR,exist_ok=True); return _DEFAULT_ROM_DIR
    except OSError: return _SCRIPT_DIR

R4300_CP0_REG_NAMES={0:"Index",1:"Random",2:"EntryLo0",3:"EntryLo1",4:"Context",5:"PageMask",6:"Wired",7:"Reserved_7",8:"BadVAddr",9:"Count",10:"EntryHi",11:"Compare",12:"Status",13:"Cause",14:"EPC",15:"PRId",16:"Config",17:"LLAddr",30:"ErrorEPC"}

class N64Opcode:
    __slots__=("word","op","rs","rt","rd","sa","funct","imm","simm","target","instr_id")
    def __init__(self,word):
        self.word=word&MASK_32; self.op=(self.word>>26)&0x3F; self.rs=(self.word>>21)&0x1F; self.rt=(self.word>>16)&0x1F
        self.rd=(self.word>>11)&0x1F; self.sa=(self.word>>6)&0x1F; self.funct=self.word&0x3F; self.imm=self.word&MASK_16; self.simm=sign16(self.imm); self.target=self.word&0x03FFFFFF
        if self.op==0: self.instr_id=_ID_SPECIAL|self.funct
        elif self.op==1: self.instr_id=_ID_REGIMM|self.rt
        elif self.op==0x10:
            if self.rs==0x10: self.instr_id=_ID_COP0_CO|self.funct
            else: self.instr_id=_ID_COP0_RS|self.rs
        elif self.op==0x11:
            if self.rs in _FPU_FMT_MAP: self.instr_id=_ID_FPU|(_FPU_FMT_MAP[self.rs]<<6)|self.funct
            elif self.rs==0x08: self.instr_id=_ID_COP1_BC|self.rt
            else: self.instr_id=_ID_COP1_RS|self.rs
        else: self.instr_id=_ID_PRIMARY|self.op
    def target_addr(self,pc): return u32(((pc+4)&0xF0000000)|(self.target<<2))
    def branch_addr(self,pc): return u32(pc+4+(self.simm<<2))


def get_opcode(word: int) -> N64Opcode:
    """Cached decode — tight boot/delay loops re-hit the same words constantly."""
    word &= MASK_32
    o = _OPCODE_CACHE.get(word)
    if o is not None:
        return o
    o = N64Opcode(word)
    if len(_OPCODE_CACHE) < _OPCODE_CACHE_MAX:
        _OPCODE_CACHE[word] = o
    return o


# ── DeviceBus with N64 register MMIO ──
class DeviceBus:
    def __init__(self, core):
        self.core = core
        self.regs = {}
        self.hw_interrupts = 0
        self.mi_intr_mask = 0
        self.mi_mode = 0
        self.mi_version = 0x02020102
        self.sp_status = SP_STATUS_HALT
        self.dpc_status = 0
        self.dps_regs = {}
        self.vi_field_serration = 0
        self.half_line = 0
        self.sp_dma_busy = False
        self.reset()

    def reset(self):
        self.regs.clear()
        self.hw_interrupts = 0
        self.mi_intr_mask = 0
        self.mi_mode = 0
        self.sp_status = SP_STATUS_HALT
        self.dpc_status = 0
        self.dps_regs.clear()
        self.vi_field_serration = 0
        self.half_line = 0
        self.sp_dma_busy = False
        self.regs[VI_ORIGIN] = 0
        self.regs[VI_WIDTH] = 320
        self.regs[VI_V_CURRENT] = 0x3FF
        self.regs[VI_INTR] = 0x3FF
        self.core._vi_origin_set = False

    def v_to_p(self, addr):
        addr &= MASK_32
        # KSEG0/KSEG1 fast path (most game code + RDRAM mirrors).
        if addr >= 0x80000000:
            seg = addr >> 29
            if seg == 0b100 or seg == 0b101:
                return addr & 0x1FFFFFFF
        else:
            seg = addr >> 29
            if seg in (0b100, 0b101):
                return addr & 0x1FFFFFFF
        tlb = self.core.cpu.tlb
        asid = self.core.cpu.cp0[CP0_ENTRYHI] & 0xFF
        vpn2 = (addr >> 13) & 0x7FFFF
        for entry in tlb:
            if entry.mask:
                extra = ((entry.mask >> 12) & 1) | ((entry.mask >> 13) & 1)
                if extra:
                    ms = 13 - extra
                    vpn2_m = (addr >> ms) & (0x7FFFF >> extra)
                    ev = entry.vpn2 >> extra
                    if ev == vpn2_m and (entry.g or entry.asid == asid):
                        eo = (addr >> (12 + extra)) & 1
                        offset_mask = (1 << (12 + extra)) - 1
                        if eo == 0 and entry.v0:
                            return ((entry.pfn0 >> extra) << (12 + extra)) | (addr & offset_mask)
                        if eo == 1 and entry.v1:
                            return ((entry.pfn1 >> extra) << (12 + extra)) | (addr & offset_mask)
            elif entry.vpn2 == vpn2 and (entry.g or entry.asid == asid):
                eo = (addr >> 12) & 1
                if eo == 0 and entry.v0:
                    return (entry.pfn0 << 12) | (addr & 0xFFF)
                if eo == 1 and entry.v1:
                    return (entry.pfn1 << 12) | (addr & 0xFFF)
        return addr & 0x1FFFFFFF

    def read_u8(self, addr):
        p = self.v_to_p(addr)
        if 0 <= p < RDRAM_SIZE: return self.core.rdram[p]
        if 0x04000000 <= p < 0x04002000:
            off = p - 0x04000000
            return (self.core.rsp_dmem if off < 0x1000 else self.core.rsp_imem)[off & 0xFFF]
        if 0x10000000 <= p < 0x10000000 + len(self.core.rom): return self.core.rom[p - 0x10000000]
        if 0x1FC007C0 <= p < 0x1FC007C0 + PIF_RAM_SIZE: return self.core.pif_ram[p - 0x1FC007C0]
        return 0

    def read_u16(self, addr):
        p = self.v_to_p(addr)
        rdram = self.core.rdram
        if 0 <= p < RDRAM_SIZE - 1: return (rdram[p] << 8) | rdram[p + 1]
        if 0x04000000 <= p < 0x04002000 - 1:
            off = p - 0x04000000
            buf = self.core.rsp_dmem if off < 0x1000 else self.core.rsp_imem
            return (buf[off & 0xFFF] << 8) | buf[(off & 0xFFF) + 1]
        return 0

    def read_u32(self, addr):
        # UltraHLE OS segment: thread RA lands on PATCH(osStopCurrentThread).
        if (addr & 0x1FFFFFFF) == (ULTRAHLE_OS_SEG & 0x1FFFFFFF):
            return make_ultrahle_patch(28)
        p = self.v_to_p(addr)
        rdram = self.core.rdram
        if p <= RDRAM_SIZE - 4:
            # Hot path: RDRAM fetch without bounds re-checks in the common case.
            return (rdram[p] << 24) | (rdram[p + 1] << 16) | (rdram[p + 2] << 8) | rdram[p + 3]
        if 0x04000000 <= p < 0x04002000:
            off = p & 0xFFF
            buf = self.core.rsp_dmem if p < 0x04001000 else self.core.rsp_imem
            return (buf[off] << 24) | (buf[off + 1] << 16) | (buf[off + 2] << 8) | buf[off + 3]
        if 0x04040000 <= p <= 0x048FFFFF: return self._read_mmio(p)
        roff = p - 0x10000000
        rom = self.core.rom
        if 0 <= roff <= len(rom) - 4:
            return (rom[roff] << 24) | (rom[roff + 1] << 16) | (rom[roff + 2] << 8) | rom[roff + 3]
        return 0

    def read_u64(self, addr): return (self.read_u32(addr) << 32) | self.read_u32(addr + 4)

    def _read_mmio(self, p):
        al = p & ~3
        if al == SP_STATUS: return self.sp_status
        if al in (SP_DMA_FULL, SP_DMA_BUSY): return 0
        if al == SP_PC: return self.core.rsp_pc
        if al == DPC_STATUS: return self.dpc_status
        if al == MI_MODE: return self.mi_mode
        if al == MI_VERSION: return self.mi_version
        if al == MI_INTR: return self.hw_interrupts
        if al == MI_INTR_MASK: return self.mi_intr_mask
        if al == VI_V_CURRENT: return self.half_line
        if VI_STATUS <= al <= VI_Y_SCALE: return self.regs.get(al, 0)
        if AI_DRAM_ADDR <= al <= AI_BITRATE: return self.regs.get(al, 0)
        if al == AI_STATUS: return self.regs.get(al, 0)
        if PI_DRAM_ADDR <= al <= PI_DOM2_RLS: return self.regs.get(al, 0)
        if al == SI_STATUS: return 0
        if SI_DRAM_ADDR <= al <= SI_PIF_ADDR_WR: return self.regs.get(al, 0)
        if RI_MODE <= al <= RI_WERROR: return self.regs.get(al, 0)
        if al in (DPC_START, DPC_END, DPC_CURRENT, DPC_CLOCK, DPC_BUFBUSY, DPC_PIPEBUSY, DPC_TMEM): return self.regs.get(al, 0)
        if al in (DPS_TBIST, DPS_TEST_MODE, DPS_BUFTEST, DPS_DETAIL): return self.dps_regs.get(al, 0)
        return self.regs.get(al, 0)

    def write_u8(self, addr, val):
        p = self.v_to_p(addr)
        val &= MASK_8
        if 0 <= p < RDRAM_SIZE: self.core.rdram[p] = val; return
        if 0x04000000 <= p < 0x04002000:
            off = p & 0xFFF
            buf = self.core.rsp_dmem if p < 0x04001000 else self.core.rsp_imem
            buf[off] = val; return
        if 0x1FC007C0 <= p < 0x1FC007C0 + PIF_RAM_SIZE: self.core.pif_ram[p - 0x1FC007C0] = val

    def write_u16(self, addr, val):
        p = self.v_to_p(addr)
        if 0 <= p < RDRAM_SIZE - 1:
            rdram = self.core.rdram; val &= MASK_16
            rdram[p] = (val >> 8) & MASK_8; rdram[p + 1] = val & MASK_8; return
        if 0x04000000 <= p < 0x04002000 - 1:
            off = p & 0xFFF; val &= MASK_16
            buf = self.core.rsp_dmem if p < 0x04001000 else self.core.rsp_imem
            buf[off] = (val >> 8) & MASK_8; buf[off + 1] = val & MASK_8

    def write_u32(self, addr, val):
        p = self.v_to_p(addr)
        rdram = self.core.rdram
        if p <= RDRAM_SIZE - 4 >= 0:
            val &= MASK_32
            rdram[p] = (val >> 24) & MASK_8; rdram[p + 1] = (val >> 16) & MASK_8
            rdram[p + 2] = (val >> 8) & MASK_8; rdram[p + 3] = val & MASK_8; return
        if 0x04000000 <= p < 0x04002000:
            off = p & 0xFFF; val &= MASK_32
            buf = self.core.rsp_dmem if p < 0x04001000 else self.core.rsp_imem
            buf[off] = (val >> 24) & MASK_8; buf[off + 1] = (val >> 16) & MASK_8
            buf[off + 2] = (val >> 8) & MASK_8; buf[off + 3] = val & MASK_8; return
        if 0x04040000 <= p <= 0x048FFFFF: self._write_mmio(p, val)

    def write_u64(self, addr, val):
        val &= MASK_64; self.write_u32(addr, (val >> 32) & MASK_32); self.write_u32(addr + 4, val & MASK_32)

    def _change_sp_status(self, mv):
        if mv & SP_CLR_HALT: self.sp_status &= ~SP_STATUS_HALT
        if mv & SP_SET_HALT: self.sp_status |= SP_STATUS_HALT
        if mv & SP_CLR_BROKE: self.sp_status &= ~SP_STATUS_BROKE
        if mv & SP_CLR_INTR: self.hw_interrupts &= ~MI_INTR_SP
        if mv & SP_CLR_SSTEP: self.sp_status &= ~SP_STATUS_SSTEP
        if mv & SP_SET_SSTEP: self.sp_status |= SP_STATUS_SSTEP
        if mv & SP_CLR_INTR_BREAK: self.sp_status &= ~SP_STATUS_INTR_BREAK
        if mv & SP_SET_INTR_BREAK: self.sp_status |= SP_STATUS_INTR_BREAK
        for i in range(8):
            clr = [SP_CLR_SIG0,SP_CLR_SIG1,SP_CLR_SIG2,SP_CLR_SIG3,SP_CLR_SIG4,SP_CLR_SIG5,SP_CLR_SIG6,SP_CLR_SIG7][i]
            set_ = [SP_SET_SIG0,SP_SET_SIG1,SP_SET_SIG2,SP_SET_SIG3,SP_SET_SIG4,SP_SET_SIG5,SP_SET_SIG6,SP_SET_SIG7][i]
            if mv & clr: self.sp_status &= ~(0x80 << i)
            if mv & set_: self.sp_status |= (0x80 << i)
        if (mv & SP_SET_SIG0) and self.core.audio_signal: self.hw_interrupts |= MI_INTR_SP
        if not (self.sp_status & SP_STATUS_HALT): self.core.process_rsp()

    def _change_dpc_status(self, mv):
        if mv & DPC_CLR_XBUS_DMEM_DMA: self.dpc_status &= ~DPC_STATUS_XBUS_DMEM_DMA
        if mv & DPC_SET_XBUS_DMEM_DMA: self.dpc_status |= DPC_STATUS_XBUS_DMEM_DMA
        if mv & DPC_CLR_FREEZE: self.dpc_status &= ~DPC_STATUS_FREEZE
        if mv & DPC_SET_FREEZE: self.dpc_status |= DPC_STATUS_FREEZE
        if mv & DPC_CLR_FLUSH: self.dpc_status &= ~DPC_STATUS_FLUSH
        if mv & DPC_SET_FLUSH: self.dpc_status |= DPC_STATUS_FLUSH
        if (mv & DPC_CLR_FREEZE) and not (self.sp_status & SP_STATUS_HALT) and not (self.sp_status & SP_STATUS_BROKE):
            self.core.process_rsp()

    def _change_mi_mode(self, mv):
        if mv & MI_CLR_INIT: self.mi_mode &= ~MI_MODE_INIT
        if mv & MI_SET_INIT: self.mi_mode |= MI_MODE_INIT
        if mv & MI_CLR_EBUS: self.mi_mode &= ~MI_MODE_EBUS
        if mv & MI_SET_EBUS: self.mi_mode |= MI_MODE_EBUS
        if mv & MI_CLR_DP_INTR: self.hw_interrupts &= ~MI_INTR_DP
        if mv & MI_CLR_RDRAM: self.mi_mode &= ~MI_MODE_RDRAM
        if mv & MI_SET_RDRAM: self.mi_mode |= MI_MODE_RDRAM

    def _change_mi_intr_mask(self, mv):
        if mv & MI_INTR_MASK_CLR_SP: self.mi_intr_mask &= ~MI_INTR_SP
        if mv & MI_INTR_MASK_SET_SP: self.mi_intr_mask |= MI_INTR_SP
        if mv & MI_INTR_MASK_CLR_SI: self.mi_intr_mask &= ~MI_INTR_SI
        if mv & MI_INTR_MASK_SET_SI: self.mi_intr_mask |= MI_INTR_SI
        if mv & MI_INTR_MASK_CLR_AI: self.mi_intr_mask &= ~MI_INTR_AI
        if mv & MI_INTR_MASK_SET_AI: self.mi_intr_mask |= MI_INTR_AI
        if mv & MI_INTR_MASK_CLR_VI: self.mi_intr_mask &= ~MI_INTR_VI
        if mv & MI_INTR_MASK_SET_VI: self.mi_intr_mask |= MI_INTR_VI
        if mv & MI_INTR_MASK_CLR_PI: self.mi_intr_mask &= ~MI_INTR_PI
        if mv & MI_INTR_MASK_SET_PI: self.mi_intr_mask |= MI_INTR_PI
        if mv & MI_INTR_MASK_CLR_DP: self.mi_intr_mask &= ~MI_INTR_DP
        if mv & MI_INTR_MASK_SET_DP: self.mi_intr_mask |= MI_INTR_DP

    def _write_mmio(self, p, val):
        al = p & ~3
        if al in (SP_MEM_ADDR, SP_DRAM_ADDR, SP_RD_LEN, SP_WR_LEN, SP_SEMAPHORE, SP_PC, SP_IBIST):
            self.regs[al] = val
            if al == SP_RD_LEN: self.core.trigger_sp_dma(to_rsp=True)
            elif al == SP_WR_LEN: self.core.trigger_sp_dma(to_rsp=False)
            elif al == SP_PC: self.core.rsp_pc = val
        elif al == SP_STATUS: self._change_sp_status(val)
        elif al == DPC_STATUS: self._change_dpc_status(val)
        elif al in (DPC_START, DPC_END, DPC_CURRENT, DPC_CLOCK, DPC_BUFBUSY, DPC_PIPEBUSY, DPC_TMEM):
            if al == DPC_END: self.core.process_rdp(); self.regs[DPC_CURRENT] = val
            self.regs[al] = val
        elif al in (DPS_TBIST, DPS_TEST_MODE, DPS_BUFTEST, DPS_DETAIL): self.dps_regs[al] = val
        elif al == MI_MODE: self._change_mi_mode(val)
        elif al == MI_INTR: self.hw_interrupts &= ~val
        elif al == MI_INTR_MASK: self._change_mi_intr_mask(val)
        elif al == VI_ORIGIN:
            self.regs[VI_ORIGIN] = val
            if (val & 0xFFFFFF) != 0:
                self.core._vi_origin_set = True
                # Present as soon as the game programs a framebuffer — don't wait
                # for the next VI retrace or the UI stays on the Booting prompt.
                self.core.render_vi()
        elif al in (VI_STATUS, VI_WIDTH, VI_BURST, VI_V_SYNC, VI_H_SYNC, VI_LEAP, VI_H_START, VI_V_START, VI_V_BURST, VI_X_SCALE, VI_Y_SCALE):
            self.regs[al] = val
            if al == VI_WIDTH and (self.regs.get(VI_ORIGIN, 0) & 0xFFFFFF):
                self.core.render_vi()
        elif al == VI_INTR: self.regs[VI_INTR] = val & 0x3FF; self.half_line = 0
        elif al == AI_DRAM_ADDR: self.regs[AI_DRAM_ADDR] = val & 0x00FFFFFF
        elif al == AI_LEN: self.regs[AI_LEN] = val; self.core.process_audio()
        elif al == AI_CONTROL: self.regs[AI_CONTROL] = val; self.regs[AI_STATUS] = self.regs.get(AI_STATUS,0) & ~AI_STATUS_DMA_BUSY
        elif al in (AI_DACRATE, AI_BITRATE): self.regs[al] = val
        elif al == PI_DRAM_ADDR: self.regs[PI_DRAM_ADDR] = val & 0x00FFFFFF
        elif al == PI_CART_ADDR: self.regs[PI_CART_ADDR] = val
        elif al == PI_RD_LEN: self.regs[PI_RD_LEN] = val; self.core.trigger_pi_dma()
        elif al == PI_WR_LEN: self.regs[PI_WR_LEN] = val; self.core.trigger_pi_dma()
        elif al == PI_STATUS:
            if val & 1: regsval = self.regs.get(PI_STATUS,0) & ~1
            if val & 2: self.hw_interrupts &= ~MI_INTR_PI
        elif PI_DOM1_LAT <= al <= PI_DOM2_RLS: self.regs[al] = val
        elif al == SI_DRAM_ADDR: self.regs[SI_DRAM_ADDR] = val
        elif al == SI_PIF_ADDR_RD: self.core.trigger_si_dma(read_pif=True)
        elif al == SI_PIF_ADDR_WR: self.core.trigger_si_dma(read_pif=False)
        elif RI_MODE <= al <= RI_WERROR: self.regs[al] = val
        else: self.regs[al] = val

# ── CPUCore (R4300i interpreter) ──
class CPUCore:
    def __init__(self, core):
        self.core = core
        self.gpr = [0] * 32
        self.fpr = [0] * 32
        self.cp0 = [0] * 32
        self.fcr0 = 0x00000511
        self.fcr31 = 0
        self.hi = 0
        self.lo = 0
        self.pc = 0
        self.next_pc = 4
        self.llbit = False
        self.lladdr = 0
        self.tlb = [TLBEntry() for _ in range(32)]
        self.reset()

    def reset(self):
        self.gpr = [0] * 32; self.fpr = [0] * 32; self.cp0 = [0] * 32
        self.fcr0 = 0x00000511; self.fcr31 = 0; self.hi = 0; self.lo = 0; self.pc = 0; self.next_pc = 4
        self.cp0[CP0_PRID] = 0x00000B00; self.cp0[CP0_STATUS] = 0x34000000; self.cp0[CP0_CONFIG] = 0x7006E463
        self.cp0[CP0_WIRED] = 0; self.cp0[CP0_CONTEXT] = 0x007FFFF0; self.cp0[CP0_EPC] = 0xFFFFFFFF
        self.cp0[CP0_BADVADDR] = 0xFFFFFFFF; self.cp0[CP0_ERROREPC] = 0xFFFFFFFF; self.cp0[CP0_CAUSE] = 0xB000005C
        self.llbit = False; self.lladdr = 0; self.tlb = [TLBEntry() for _ in range(32)]

    def step(self):
        bus = self.core.bus
        cp0 = self.cp0
        status = cp0[CP0_STATUS]
        # RCP (MI) interrupts all share CPU IP2. Timer uses IP7 via COMPARE.
        pending_rcp = bus.hw_interrupts & bus.mi_intr_mask & 0x3F
        if pending_rcp:
            cp0[CP0_CAUSE] = (cp0[CP0_CAUSE] & ~CAUSE_IP2) | CAUSE_IP2
        else:
            cp0[CP0_CAUSE] &= ~CAUSE_IP2
        if (status & STATUS_IE) and not (status & (STATUS_EXL | STATUS_ERL)):
            cause = cp0[CP0_CAUSE]
            # Fire if any Cause IP bit is enabled in Status IM (bits 8..15).
            if (cause & status & 0xFF00) != 0:
                cp0[CP0_STATUS] |= STATUS_EXL
                cp0[CP0_EPC] = self.pc
                use_bev = bool(cp0[CP0_STATUS] & STATUS_BEV)
                self.pc = 0xBFC00380 if use_bev else 0x80000180
                self.next_pc = self.pc + 4
        word = bus.read_u32(self.pc)
        self.execute(get_opcode(word))
        self.gpr[0] = 0
        # COUNT ticks ~2x per instruction on real HW; keep 1 for interpreter scale,
        # then catch up to full N64 frame cycles in step_frame.
        count = u32(cp0[CP0_COUNT] + 1)
        cp0[CP0_COUNT] = count
        if count == cp0[CP0_COMPARE]:
            cp0[CP0_CAUSE] |= CAUSE_IP7  # timer interrupt only — never fake SP

    def step_block(self, n: int) -> int:
        """Run up to n instructions; return how many actually executed."""
        ran = 0
        g0 = self.gpr
        while ran < n:
            self.step()
            g0[0] = 0
            ran += 1
            if not self.core.running:
                break
        return ran

    def _branch(self, target): self.next_pc = u32(target)
    def _skip_likely(self): self.pc = u32(self.pc + 4); self.next_pc = u32(self.pc + 4)

    def _write_tlb_entry(self, index):
        idx = index % 32; hi = self.cp0[CP0_ENTRYHI]; lo0 = self.cp0[CP0_ENTRYLO0]; lo1 = self.cp0[CP0_ENTRYLO1]
        pm = self.cp0[CP0_PAGEMASK]
        self.tlb[idx].mask = pm; self.tlb[idx].vpn2 = (hi >> 13) & 0x7FFFF; self.tlb[idx].asid = hi & 0xFF
        self.tlb[idx].g = bool((lo0 & 1) and (lo1 & 1))
        self.tlb[idx].pfn0 = (lo0 >> 6) & 0xFFFFF; self.tlb[idx].c0 = (lo0 >> 3) & 7
        self.tlb[idx].d0 = bool((lo0 >> 2) & 1); self.tlb[idx].v0 = bool((lo0 >> 1) & 1)
        self.tlb[idx].pfn1 = (lo1 >> 6) & 0xFFFFF; self.tlb[idx].c1 = (lo1 >> 3) & 7
        self.tlb[idx].d1 = bool((lo1 >> 2) & 1); self.tlb[idx].v1 = bool((lo1 >> 1) & 1)

    def _raise_exception(self, exc_code, old_pc):
        self.cp0[CP0_CAUSE] = (self.cp0[CP0_CAUSE] & ~0x80000000) | (exc_code << 2)
        self.cp0[CP0_EPC] = old_pc; self.cp0[CP0_STATUS] |= STATUS_EXL
        use_bev = bool(self.cp0[CP0_STATUS] & STATUS_BEV)
        self.pc = 0x80000180 if not use_bev else 0xBFC00380; self.next_pc = self.pc + 4

    def _test_cop1_usable(self): return bool(self.cp0[CP0_STATUS] & STATUS_CU1)
    def _clear_fp_cause(self): self.fcr31 &= ~0x3F000
    def _set_fp_cause(self, cause): self.fcr31 &= ~0x3F000; self.fcr31 |= (cause & 0x3F) << 12
    def _set_fp_flags(self, cause): self.fcr31 |= (cause & 0x3F) << 2

    def execute(self, o):
        old_pc = self.pc
        self.pc = self.next_pc
        self.next_pc = u32(self.next_pc + 4)
        h = _DISPATCH[o.instr_id]
        if h is not None:
            h(self, o, old_pc, self.gpr)
        elif o.op in (0x10, 0x11, 0x12, 0x13):
            self._raise_exception(11, old_pc)
        else:
            self._raise_exception(10, old_pc)

# ── Instruction handlers ──
def _h_NOP(cpu, o, old_pc, g): pass
def _h_LUI(cpu, o, old_pc, g): g[o.rt] = sx32_to_64(o.imm << 16)
def _h_ORI(cpu, o, old_pc, g): g[o.rt] = u64(g[o.rs] | o.imm)
def _h_ANDI(cpu, o, old_pc, g): g[o.rt] = u64(g[o.rs] & o.imm)
def _h_XORI(cpu, o, old_pc, g): g[o.rt] = u64(g[o.rs] ^ o.imm)
def _h_ADDI(cpu, o, old_pc, g): g[o.rt] = sx32_to_64(u32(g[o.rs] + o.simm))
def _h_ADDIU(cpu, o, old_pc, g): g[o.rt] = sx32_to_64(u32(g[o.rs] + o.simm))
def _h_DADDI(cpu, o, old_pc, g): g[o.rt] = u64(g[o.rs] + o.simm)
def _h_DADDIU(cpu, o, old_pc, g): g[o.rt] = u64(g[o.rs] + o.simm)
def _h_SLTI(cpu, o, old_pc, g): g[o.rt] = 1 if sign64(g[o.rs]) < o.simm else 0
def _h_SLTIU(cpu, o, old_pc, g): g[o.rt] = 1 if g[o.rs] < u64(o.simm) else 0
def _h_LB(cpu, o, old_pc, g): g[o.rt] = sx8_to_64(cpu.core.bus.read_u8(g[o.rs] + o.simm))
def _h_LBU(cpu, o, old_pc, g): g[o.rt] = cpu.core.bus.read_u8(g[o.rs] + o.simm)
def _h_LH(cpu, o, old_pc, g): g[o.rt] = sx16_to_64(cpu.core.bus.read_u16(g[o.rs] + o.simm))
def _h_LHU(cpu, o, old_pc, g): g[o.rt] = cpu.core.bus.read_u16(g[o.rs] + o.simm)
def _h_LW(cpu, o, old_pc, g): g[o.rt] = sx32_to_64(cpu.core.bus.read_u32(g[o.rs] + o.simm))
def _h_LWU(cpu, o, old_pc, g): g[o.rt] = cpu.core.bus.read_u32(g[o.rs] + o.simm)
def _h_LD(cpu, o, old_pc, g): g[o.rt] = cpu.core.bus.read_u64(g[o.rs] + o.simm)
def _h_LWL(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm); off = addr & 3; al = addr & ~3
    val = cpu.core.bus.read_u32(al)
    g[o.rt] = sx32_to_64((u32(g[o.rt]) & _lwl_mask[off]) | (val << _lwl_shift[off]))
def _h_LWR(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm); off = addr & 3; al = addr & ~3
    val = cpu.core.bus.read_u32(al)
    g[o.rt] = sx32_to_64((u32(g[o.rt]) & _lwr_mask[off]) | (val >> _lwr_shift[off]))
def _h_LDL(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm); off = addr & 7; al = addr & ~7
    val = cpu.core.bus.read_u64(al)
    g[o.rt] = (g[o.rt] & _ldl_mask[off]) | (val << _ldl_shift[off])
def _h_LDR(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm); off = addr & 7; al = addr & ~7
    val = cpu.core.bus.read_u64(al)
    g[o.rt] = (g[o.rt] & _ldr_mask[off]) | (val >> _ldr_shift[off])
def _h_LL(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm); g[o.rt] = sx32_to_64(cpu.core.bus.read_u32(addr))
    cpu.llbit = True; cpu.lladdr = addr & ~3
def _h_LLD(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm); g[o.rt] = cpu.core.bus.read_u64(addr)
    cpu.llbit = True; cpu.lladdr = addr & ~7
def _h_LWC1(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc); return
    addr = u32(g[o.rs] + o.simm)
    cpu.fpr[o.rt] = u64((cpu.fpr[o.rt] & 0xFFFFFFFF00000000) | (cpu.core.bus.read_u32(addr) & MASK_32))
def _h_LDC1(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc); return
    cpu.fpr[o.rt] = cpu.core.bus.read_u64(u32(g[o.rs] + o.simm))
def _h_SB(cpu, o, old_pc, g): cpu.core.bus.write_u8(u32(g[o.rs] + o.simm), u8(g[o.rt]))
def _h_SH(cpu, o, old_pc, g): cpu.core.bus.write_u16(u32(g[o.rs] + o.simm), u16(g[o.rt]))
def _h_SW(cpu, o, old_pc, g): cpu.core.bus.write_u32(u32(g[o.rs] + o.simm), u32(g[o.rt]))
def _h_SD(cpu, o, old_pc, g): cpu.core.bus.write_u64(u32(g[o.rs] + o.simm), g[o.rt])
def _h_SWL(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm); off = addr & 3; al = addr & ~3
    val = cpu.core.bus.read_u32(al)
    val = (val & _swl_mask[off]) | (u32(g[o.rt]) >> _swl_shift[off])
    cpu.core.bus.write_u32(al, val)
def _h_SWR(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm); off = addr & 3; al = addr & ~3
    val = cpu.core.bus.read_u32(al)
    val = (val & _swr_mask[off]) | (u32(g[o.rt]) << _swr_shift[off])
    cpu.core.bus.write_u32(al, val)
def _h_SDL(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm); off = addr & 7; al = addr & ~7
    val = cpu.core.bus.read_u64(al)
    val = (val & _sdl_mask[off]) | (g[o.rt] >> _sdl_shift[off])
    cpu.core.bus.write_u64(al, val)
def _h_SDR(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm); off = addr & 7; al = addr & ~7
    val = cpu.core.bus.read_u64(al)
    val = (val & _sdr_mask[off]) | (g[o.rt] << _sdr_shift[off])
    cpu.core.bus.write_u64(al, val)
def _h_SC(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm)
    if cpu.llbit and (addr & ~3) == cpu.lladdr:
        cpu.core.bus.write_u32(addr, u32(g[o.rt])); g[o.rt] = 1
    else: g[o.rt] = 0
    cpu.llbit = False
def _h_SCD(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm)
    if cpu.llbit and (addr & ~7) == cpu.lladdr:
        cpu.core.bus.write_u64(addr, g[o.rt]); g[o.rt] = 1
    else: g[o.rt] = 0
    cpu.llbit = False
def _h_SWC1(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc); return
    cpu.core.bus.write_u32(u32(g[o.rs] + o.simm), u32(cpu.fpr[o.rt]))
def _h_SDC1(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc); return
    cpu.core.bus.write_u64(u32(g[o.rs] + o.simm), cpu.fpr[o.rt])

# SPECIAL opcodes
def _h_SLL(cpu, o, old_pc, g): g[o.rd] = sx32_to_64(u32(g[o.rt]) << o.sa)
def _h_SRL(cpu, o, old_pc, g): g[o.rd] = sx32_to_64(u32(g[o.rt]) >> o.sa)
def _h_SRA(cpu, o, old_pc, g): g[o.rd] = sx32_to_64(sign32(g[o.rt]) >> o.sa)
def _h_SLLV(cpu, o, old_pc, g): g[o.rd] = sx32_to_64(u32(g[o.rt]) << (g[o.rs] & 0x1F))
def _h_SRLV(cpu, o, old_pc, g): g[o.rd] = sx32_to_64(u32(g[o.rt]) >> (g[o.rs] & 0x1F))
def _h_SRAV(cpu, o, old_pc, g): g[o.rd] = sx32_to_64(sign32(g[o.rt]) >> (g[o.rs] & 0x1F))
def _h_DSLLV(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rt] << (g[o.rs] & 0x3F))
def _h_DSRLV(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rt] >> (g[o.rs] & 0x3F))
def _h_DSRAV(cpu, o, old_pc, g): g[o.rd] = u64(sign64(g[o.rt]) >> (g[o.rs] & 0x3F))
def _h_DSLL(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rt] << o.sa)
def _h_DSRL(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rt] >> o.sa)
def _h_DSRA(cpu, o, old_pc, g): g[o.rd] = u64(sign64(g[o.rt]) >> o.sa)
def _h_DSLL32(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rt] << (o.sa + 32))
def _h_DSRL32(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rt] >> (o.sa + 32))
def _h_DSRA32(cpu, o, old_pc, g): g[o.rd] = u64(sign64(g[o.rt]) >> (o.sa + 32))
def _h_ADD(cpu, o, old_pc, g): g[o.rd] = sx32_to_64(u32(g[o.rs] + g[o.rt]))
def _h_ADDU(cpu, o, old_pc, g): g[o.rd] = sx32_to_64(u32(g[o.rs] + g[o.rt]))
def _h_SUB(cpu, o, old_pc, g): g[o.rd] = sx32_to_64(u32(g[o.rs] - g[o.rt]))
def _h_SUBU(cpu, o, old_pc, g): g[o.rd] = sx32_to_64(u32(g[o.rs] - g[o.rt]))
def _h_DADD(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rs] + g[o.rt])
def _h_DADDU(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rs] + g[o.rt])
def _h_DSUB(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rs] - g[o.rt])
def _h_DSUBU(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rs] - g[o.rt])
def _h_AND(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rs] & g[o.rt])
def _h_OR(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rs] | g[o.rt])
def _h_XOR(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rs] ^ g[o.rt])
def _h_NOR(cpu, o, old_pc, g): g[o.rd] = u64(~(g[o.rs] | g[o.rt]))
def _h_MOVZ(cpu, o, old_pc, g):
    if g[o.rt] == 0: g[o.rd] = g[o.rs]
def _h_MOVN(cpu, o, old_pc, g):
    if g[o.rt] != 0: g[o.rd] = g[o.rs]
def _h_SLT(cpu, o, old_pc, g): g[o.rd] = 1 if sign64(g[o.rs]) < sign64(g[o.rt]) else 0
def _h_SLTU(cpu, o, old_pc, g): g[o.rd] = 1 if g[o.rs] < g[o.rt] else 0
def _h_MFHI(cpu, o, old_pc, g): g[o.rd] = cpu.hi
def _h_MTHI(cpu, o, old_pc, g): cpu.hi = u64(g[o.rs])
def _h_MFLO(cpu, o, old_pc, g): g[o.rd] = cpu.lo
def _h_MTLO(cpu, o, old_pc, g): cpu.lo = u64(g[o.rs])
def _h_MULT(cpu, o, old_pc, g):
    prod = sign32(g[o.rs]) * sign32(g[o.rt])
    cpu.lo = sx32_to_64(prod & MASK_32); cpu.hi = sx32_to_64((prod >> 32) & MASK_32)
def _h_MULTU(cpu, o, old_pc, g):
    prod = u32(g[o.rs]) * u32(g[o.rt])
    cpu.lo = sx32_to_64(prod & MASK_32); cpu.hi = sx32_to_64((prod >> 32) & MASK_32)
def _h_DMULT(cpu, o, old_pc, g):
    prod = sign64(g[o.rs]) * sign64(g[o.rt]); cpu.lo = u64(prod); cpu.hi = u64(prod >> 64)
def _h_DMULTU(cpu, o, old_pc, g):
    prod = g[o.rs] * g[o.rt]; cpu.lo = u64(prod); cpu.hi = u64(prod >> 64)
def _h_DIV(cpu, o, old_pc, g):
    a_s = sign32(g[o.rs]); b_s = sign32(g[o.rt]); b = u32(g[o.rt])
    if b != 0:
        if a_s == -0x80000000 and b_s == -1: cpu.lo = sx32_to_64(-0x80000000); cpu.hi = 0
        else: cpu.lo = sx32_to_64(a_s // b_s); cpu.hi = sx32_to_64(a_s % b_s)
    else: cpu.lo = 1 if a_s < 0 else -1; cpu.hi = sx32_to_64(a_s)
def _h_DIVU(cpu, o, old_pc, g):
    a = u32(g[o.rs]); b = u32(g[o.rt])
    if b != 0: cpu.lo = sx32_to_64(a // b); cpu.hi = sx32_to_64(a % b)
    else: cpu.lo = -1; cpu.hi = sx32_to_64(a)
def _h_DDIV(cpu, o, old_pc, g):
    a = g[o.rs]; b = g[o.rt]
    if b != 0: cpu.lo = u64(sign64(a) // sign64(b)); cpu.hi = u64(sign64(a) % sign64(b))
    else: cpu.lo = 1 if sign64(a) < 0 else -1; cpu.hi = u64(a)
def _h_DDIVU(cpu, o, old_pc, g):
    a = g[o.rs]; b = g[o.rt]
    if b != 0: cpu.lo = u64(a // b); cpu.hi = u64(a % b)
    else: cpu.lo = -1; cpu.hi = u64(a)

# REGIMM
def _h_BLTZ(cpu, o, old_pc, g):
    if sign64(g[o.rs]) < 0: cpu._branch(o.branch_addr(old_pc))
def _h_BGEZ(cpu, o, old_pc, g):
    if sign64(g[o.rs]) >= 0: cpu._branch(o.branch_addr(old_pc))
def _h_BLTZL(cpu, o, old_pc, g):
    if sign64(g[o.rs]) < 0: cpu._branch(o.branch_addr(old_pc))
    else: cpu._skip_likely()
def _h_BGEZL(cpu, o, old_pc, g):
    if sign64(g[o.rs]) >= 0: cpu._branch(o.branch_addr(old_pc))
    else: cpu._skip_likely()
def _h_BLTZAL(cpu, o, old_pc, g):
    g[31] = u64(old_pc + 8)
    if sign64(g[o.rs]) < 0: cpu._branch(o.branch_addr(old_pc))
def _h_BGEZAL(cpu, o, old_pc, g):
    g[31] = u64(old_pc + 8)
    if sign64(g[o.rs]) >= 0: cpu._branch(o.branch_addr(old_pc))
def _h_BLTZALL(cpu, o, old_pc, g):
    g[31] = u64(old_pc + 8)
    if sign64(g[o.rs]) < 0: cpu._branch(o.branch_addr(old_pc))
    else: cpu._skip_likely()
def _h_BGEZALL(cpu, o, old_pc, g):
    g[31] = u64(old_pc + 8)
    if sign64(g[o.rs]) >= 0: cpu._branch(o.branch_addr(old_pc))
    else: cpu._skip_likely()
def _h_J(cpu, o, old_pc, g): cpu._branch(o.target_addr(old_pc))
def _h_JAL(cpu, o, old_pc, g):
    g[31] = u64(old_pc + 8); cpu._branch(o.target_addr(old_pc))
def _h_JR(cpu, o, old_pc, g): cpu._branch(g[o.rs])
def _h_JALR(cpu, o, old_pc, g):
    g[o.rd] = u64(old_pc + 8); cpu._branch(g[o.rs])
def _h_BEQ(cpu, o, old_pc, g):
    if g[o.rs] == g[o.rt]: cpu._branch(o.branch_addr(old_pc))
def _h_BNE(cpu, o, old_pc, g):
    if g[o.rs] != g[o.rt]: cpu._branch(o.branch_addr(old_pc))
def _h_BLEZ(cpu, o, old_pc, g):
    if sign64(g[o.rs]) <= 0: cpu._branch(o.branch_addr(old_pc))
def _h_BGTZ(cpu, o, old_pc, g):
    if sign64(g[o.rs]) > 0: cpu._branch(o.branch_addr(old_pc))
def _h_BEQL(cpu, o, old_pc, g):
    if g[o.rs] == g[o.rt]: cpu._branch(o.branch_addr(old_pc))
    else: cpu._skip_likely()
def _h_BNEL(cpu, o, old_pc, g):
    if g[o.rs] != g[o.rt]: cpu._branch(o.branch_addr(old_pc))
    else: cpu._skip_likely()
def _h_BLEZL(cpu, o, old_pc, g):
    if sign64(g[o.rs]) <= 0: cpu._branch(o.branch_addr(old_pc))
    else: cpu._skip_likely()
def _h_BGTZL(cpu, o, old_pc, g):
    if sign64(g[o.rs]) > 0: cpu._branch(o.branch_addr(old_pc))
    else: cpu._skip_likely()

# COP0
def _h_MFC0(cpu, o, old_pc, g): g[o.rt] = sx32_to_64(cpu.cp0[o.rd])
def _h_DMFC0(cpu, o, old_pc, g): g[o.rt] = u64(cpu.cp0[o.rd])
def _h_CFC0(cpu, o, old_pc, g): g[o.rt] = sx32_to_64(cpu.cp0[o.rd])
def _h_MTC0(cpu, o, old_pc, g):
    val = u32(g[o.rt]); rd = o.rd
    if rd == CP0_INDEX: cpu.cp0[rd] = val & 0x8000003F
    elif rd in (CP0_ENTRYLO0, CP0_ENTRYLO1): cpu.cp0[rd] = val & 0x3FFFFFFF
    elif rd == CP0_PAGEMASK: cpu.cp0[rd] = val & 0x01FFE000
    elif rd == CP0_WIRED: cpu.cp0[rd] = val & 0x3F; cpu.cp0[CP0_RANDOM] = 31
    elif rd == CP0_CONTEXT: cpu.cp0[rd] = (cpu.cp0[rd] & 0x7FFFFF) | (val & 0xFF800000)
    elif rd == CP0_COUNT: cpu.cp0[rd] = val
    elif rd == CP0_COMPARE: cpu.cp0[rd] = val; cpu.cp0[CP0_CAUSE] &= ~CAUSE_IP7
    elif rd in (CP0_ENTRYHI, CP0_STATUS, CP0_CAUSE, CP0_EPC, CP0_ERROREPC, CP0_LLADDR, CP0_CONFIG): cpu.cp0[rd] = val
    elif rd in (28, 29): cpu.cp0[rd] = val
def _h_DMTC0(cpu, o, old_pc, g):
    val = u64(g[o.rt]); rd = o.rd
    if rd == CP0_ENTRYHI: cpu.cp0[rd] = val & 0xFFFFFFFF
    elif rd == CP0_CONTEXT: cpu.cp0[rd] = (cpu.cp0[rd] & 0x7FFFFF) | (val & 0xFFFFFFFFFF800000)
    else: cpu.cp0[rd] = val
def _h_CTC0(cpu, o, old_pc, g): cpu.cp0[o.rd] = u32(g[o.rt])
def _h_BC0(cpu, o, old_pc, g):
    # VR4300 COP0 has no useful condition bit; treat condition as false.
    tf = o.rt & 1; likely = bool(o.rt & 2); cond = False
    if cond == bool(tf): cpu._branch(o.branch_addr(old_pc))
    elif likely: cpu._skip_likely()
def _h_ERET(cpu, o, old_pc, g):
    if cpu.cp0[CP0_STATUS] & STATUS_ERL:
        target = cpu.cp0[CP0_ERROREPC]
        cpu.cp0[CP0_STATUS] &= ~STATUS_ERL
    else:
        target = cpu.cp0[CP0_EPC]
        cpu.cp0[CP0_STATUS] &= ~STATUS_EXL
    cpu.pc = u32(target); cpu.next_pc = u32(cpu.pc + 4)
def _h_TLBWI(cpu, o, old_pc, g): cpu._write_tlb_entry(cpu.cp0[CP0_INDEX] & 0x1F)
def _h_TLBWR(cpu, o, old_pc, g):
    w = cpu.cp0[CP0_WIRED] & 0x1F; cpu._write_tlb_entry(random.randint(w, 31))
def _h_TLBP(cpu, o, old_pc, g):
    hi = cpu.cp0[CP0_ENTRYHI]; vpn2 = (hi >> 13) & 0x7FFFF; asid = hi & 0xFF
    match_i = -1
    for i, entry in enumerate(cpu.tlb):
        if entry.vpn2 == vpn2 and (entry.g or entry.asid == asid): match_i = i; break
    cpu.cp0[CP0_INDEX] = match_i if match_i >= 0 else 0x80000000
def _h_TLBR(cpu, o, old_pc, g):
    idx = cpu.cp0[CP0_INDEX] & 0x1F; entry = cpu.tlb[idx]
    cpu.cp0[CP0_PAGEMASK] = entry.mask; cpu.cp0[CP0_ENTRYHI] = (entry.vpn2 << 13) | entry.asid
    cpu.cp0[CP0_ENTRYLO0] = (entry.pfn0 << 6) | (entry.c0 << 3) | (entry.d0 << 2) | (entry.v0 << 1) | entry.g
    cpu.cp0[CP0_ENTRYLO1] = (entry.pfn1 << 6) | (entry.c1 << 3) | (entry.d1 << 2) | (entry.v1 << 1) | entry.g

# COP1
def _h_MFC1(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc); return
    g[o.rt] = sx32_to_64(cpu.fpr[o.rd] & MASK_32)
def _h_DMFC1(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc); return
    g[o.rt] = cpu.fpr[o.rd]
def _h_CFC1(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc); return
    g[o.rt] = sx32_to_64(cpu.fcr31 if o.rd == 31 else cpu.fcr0)
def _h_MTC1(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc); return
    cpu.fpr[o.rd] = u64((cpu.fpr[o.rd] & 0xFFFFFFFF00000000) | (g[o.rt] & MASK_32))
def _h_DMTC1(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc); return
    cpu.fpr[o.rd] = g[o.rt]
def _h_CTC1(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc); return
    if o.rd == 31: cpu.fcr31 = u32(g[o.rt])
    elif o.rd == 0: cpu.fcr0 = u32(g[o.rt])
def _h_BC1(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc); return
    tf = o.rt & 1; likely = bool(o.rt & 2)
    cond = bool((cpu.fcr31 >> FCR31_COND_BIT) & 1)
    if cond == bool(tf): cpu._branch(o.branch_addr(old_pc))
    elif likely: cpu._skip_likely()

# Traps
def _h_SYSCALL(cpu, o, old_pc, g): cpu._raise_exception(8, old_pc)
def _h_BREAK(cpu, o, old_pc, g): cpu._raise_exception(9, old_pc)
def _h_TGE(cpu, o, old_pc, g):
    if sign64(g[o.rs]) >= sign64(g[o.rt]): cpu._raise_exception(13, old_pc)
def _h_TGEU(cpu, o, old_pc, g):
    if g[o.rs] >= g[o.rt]: cpu._raise_exception(13, old_pc)
def _h_TLT(cpu, o, old_pc, g):
    if sign64(g[o.rs]) < sign64(g[o.rt]): cpu._raise_exception(13, old_pc)
def _h_TLTU(cpu, o, old_pc, g):
    if g[o.rs] < g[o.rt]: cpu._raise_exception(13, old_pc)
def _h_TEQ(cpu, o, old_pc, g):
    if g[o.rs] == g[o.rt]: cpu._raise_exception(13, old_pc)
def _h_TNE(cpu, o, old_pc, g):
    if g[o.rs] != g[o.rt]: cpu._raise_exception(13, old_pc)
def _h_TGEI(cpu, o, old_pc, g):
    if sign64(g[o.rs]) >= o.simm: cpu._raise_exception(13, old_pc)
def _h_TGEIU(cpu, o, old_pc, g):
    if g[o.rs] >= u64(o.simm): cpu._raise_exception(13, old_pc)
def _h_TLTI(cpu, o, old_pc, g):
    if sign64(g[o.rs]) < o.simm: cpu._raise_exception(13, old_pc)
def _h_TLTIU(cpu, o, old_pc, g):
    if g[o.rs] < u64(o.simm): cpu._raise_exception(13, old_pc)
def _h_TEQI(cpu, o, old_pc, g):
    if g[o.rs] == u64(o.simm): cpu._raise_exception(13, old_pc)
def _h_TNEI(cpu, o, old_pc, g):
    if g[o.rs] != u64(o.simm): cpu._raise_exception(13, old_pc)

# FPU format ops — full VR4300 COP1 S/D/W/L surface
def _h_FPU(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc); return
    cpu._clear_fp_cause()
    fmt_id = (o.instr_id >> 6) & 3; funct = o.instr_id & 0x3F
    fs, fd, ft = o.rd, o.sa, o.rt

    def _set_s(bits32):
        cpu.fpr[fd] = u64((cpu.fpr[fd] & 0xFFFFFFFF00000000) | (bits32 & MASK_32))

    def _cmp_set(cond):
        if cond: cpu.fcr31 |= (1 << FCR31_COND_BIT)
        else: cpu.fcr31 &= ~(1 << FCR31_COND_BIT)

    def _fp_cmp(a, b, funct):
        nan = math.isnan(a) or math.isnan(b)
        if funct in (0x30, 0x38): return False                          # C.F / C.SF
        if funct in (0x31, 0x39): return nan                            # C.UN / C.NGLE
        if funct in (0x32, 0x3A): return (not nan) and a == b           # C.EQ / C.SEQ
        if funct in (0x33, 0x3B): return nan or a == b                  # C.UEQ / C.NGL
        if funct in (0x34, 0x3C): return (not nan) and a < b            # C.OLT / C.LT
        if funct in (0x35, 0x3D): return nan or a < b                   # C.ULT / C.NGE
        if funct in (0x36, 0x3E): return (not nan) and a <= b           # C.OLE / C.LE
        if funct in (0x37, 0x3F): return nan or a <= b                  # C.ULE / C.NGT
        return False

    def _cvt_to_w(f, mode):
        if math.isnan(f) or math.isinf(f): return 0
        if mode == 0x0C: return int(round(f))
        if mode == 0x0D: return int(f)
        if mode == 0x0E: return int(math.ceil(f))
        return int(math.floor(f))

    def _cvt_to_l(f, mode):
        if math.isnan(f): return 0
        if math.isinf(f): return int(f)
        if mode == 0x08: return int(round(f))
        if mode == 0x09: return int(f)
        if mode == 0x0A: return int(math.ceil(f))
        return int(math.floor(f))

    if fmt_id == _ID_FPU_S:
        a = bits_to_f32(cpu.fpr[fs] & MASK_32)
        b = bits_to_f32(cpu.fpr[ft] & MASK_32)
        if funct == 0x00: _set_s(f32_to_bits(a + b))
        elif funct == 0x01: _set_s(f32_to_bits(a - b))
        elif funct == 0x02: _set_s(f32_to_bits(a * b))
        elif funct == 0x03:
            if b == 0.0:
                cpu._set_fp_cause(FCR31_CAUSE_DIVBYZERO); cpu._set_fp_flags(FCR31_CAUSE_DIVBYZERO)
                _set_s(f32_to_bits(float("inf") if a >= 0.0 else float("-inf")))
            else:
                _set_s(f32_to_bits(a / b))
        elif funct == 0x04: _set_s(f32_to_bits(math.sqrt(a) if a >= 0 else float("nan")))
        elif funct == 0x05: _set_s(f32_to_bits(abs(a)))
        elif funct == 0x06: _set_s(cpu.fpr[fs] & MASK_32)
        elif funct == 0x07: _set_s(f32_to_bits(-a))
        elif funct == 0x15:  # RECIP.S
            if a == 0.0: cpu._set_fp_cause(FCR31_CAUSE_DIVBYZERO); cpu._set_fp_flags(FCR31_CAUSE_DIVBYZERO)
            _set_s(f32_to_bits(1.0 / a if a != 0.0 else float("inf")))
        elif funct == 0x16:  # RSQRT.S
            if a < 0: cpu._set_fp_cause(FCR31_CAUSE_INVALID); _set_s(f32_to_bits(float("nan")))
            elif a == 0.0: cpu._set_fp_cause(FCR31_CAUSE_DIVBYZERO); _set_s(f32_to_bits(float("inf")))
            else: _set_s(f32_to_bits(1.0 / math.sqrt(a)))
        elif funct == 0x20: _set_s(cpu.fpr[fs] & MASK_32)                 # CVT.S.S
        elif funct == 0x21: cpu.fpr[fd] = f64_to_bits(a)                 # CVT.D.S
        elif funct in (0x24, 0x25):
            w = 0 if math.isnan(a) or math.isinf(a) else int(a)
            if funct == 0x25: cpu.fpr[fd] = u64(w)
            else: _set_s(u32(w))
        elif funct in (0x0C, 0x0D, 0x0E, 0x0F): _set_s(u32(_cvt_to_w(a, funct)))
        elif funct in (0x08, 0x09, 0x0A, 0x0B): cpu.fpr[fd] = u64(_cvt_to_l(a, funct))
        elif funct >= 0x30: _cmp_set(_fp_cmp(a, b, funct))

    elif fmt_id == _ID_FPU_D:
        a = bits_to_f64(cpu.fpr[fs]); b = bits_to_f64(cpu.fpr[ft])
        if funct == 0x00: cpu.fpr[fd] = f64_to_bits(a + b)
        elif funct == 0x01: cpu.fpr[fd] = f64_to_bits(a - b)
        elif funct == 0x02: cpu.fpr[fd] = f64_to_bits(a * b)
        elif funct == 0x03:
            if b == 0.0:
                cpu._set_fp_cause(FCR31_CAUSE_DIVBYZERO); cpu._set_fp_flags(FCR31_CAUSE_DIVBYZERO)
                cpu.fpr[fd] = f64_to_bits(float("inf") if a >= 0.0 else float("-inf"))
            else:
                cpu.fpr[fd] = f64_to_bits(a / b)
        elif funct == 0x04: cpu.fpr[fd] = f64_to_bits(math.sqrt(a) if a >= 0 else float("nan"))
        elif funct == 0x05: cpu.fpr[fd] = f64_to_bits(abs(a))
        elif funct == 0x06: cpu.fpr[fd] = cpu.fpr[fs]
        elif funct == 0x07: cpu.fpr[fd] = f64_to_bits(-a)
        elif funct == 0x15:
            if a == 0.0: cpu._set_fp_cause(FCR31_CAUSE_DIVBYZERO); cpu._set_fp_flags(FCR31_CAUSE_DIVBYZERO)
            cpu.fpr[fd] = f64_to_bits(1.0 / a if a != 0.0 else float("inf"))
        elif funct == 0x16:
            if a < 0: cpu._set_fp_cause(FCR31_CAUSE_INVALID); cpu.fpr[fd] = f64_to_bits(float("nan"))
            elif a == 0.0: cpu._set_fp_cause(FCR31_CAUSE_DIVBYZERO); cpu.fpr[fd] = f64_to_bits(float("inf"))
            else: cpu.fpr[fd] = f64_to_bits(1.0 / math.sqrt(a))
        elif funct == 0x20: _set_s(f32_to_bits(float(a)))               # CVT.S.D
        elif funct == 0x21: cpu.fpr[fd] = cpu.fpr[fs]                   # CVT.D.D
        elif funct in (0x24, 0x25):
            w = 0 if math.isnan(a) or math.isinf(a) else int(a)
            if funct == 0x25: cpu.fpr[fd] = u64(w)
            else: _set_s(u32(w))
        elif funct in (0x0C, 0x0D, 0x0E, 0x0F): _set_s(u32(_cvt_to_w(a, funct)))
        elif funct in (0x08, 0x09, 0x0A, 0x0B): cpu.fpr[fd] = u64(_cvt_to_l(a, funct))
        elif funct >= 0x30: _cmp_set(_fp_cmp(a, b, funct))

    elif fmt_id == _ID_FPU_W:
        # Word fixed-point source (integer in low 32 bits), not an IEEE float.
        wi = sign32(cpu.fpr[fs] & MASK_32)
        if funct == 0x20: _set_s(f32_to_bits(float(wi)))               # CVT.S.W
        elif funct == 0x21: cpu.fpr[fd] = f64_to_bits(float(wi))       # CVT.D.W
        elif funct == 0x24: _set_s(u32(wi))                            # CVT.W.W
        elif funct == 0x25: cpu.fpr[fd] = u64(wi)                      # CVT.L.W

    elif fmt_id == _ID_FPU_L:
        li = sign64(cpu.fpr[fs])
        if funct == 0x20: _set_s(f32_to_bits(float(li)))               # CVT.S.L
        elif funct == 0x21: cpu.fpr[fd] = f64_to_bits(float(li))       # CVT.D.L
        elif funct == 0x24: _set_s(u32(li))                            # CVT.W.L
        elif funct == 0x25: cpu.fpr[fd] = u64(li)                      # CVT.L.L


# ── UltraHLE OP_PATCH / OP_GROUP (primary 0x1C / 0x1D) ──
# UltraHLE rewrote libultra OS entry points to PATCH(id)=(0x1C<<26)|id.
# Encoding matches EmulatorArchive/ultrahle ULTRA.H: OP_PATCH=28, OP_GROUP=29.
ULTRAHLE_OP_PATCH = 0x1C
ULTRAHLE_OP_GROUP = 0x1D
ULTRAHLE_OS_SEG = 0x03FF0000  # UltraHLE thread-return page (PATCH 28)
ULTRAHLE_THREAD_RA = 0x03FF0000
ULTRAHLE_MQ_MAGIC = 0xFCFC1234
ULTRAHLE_MAX_THREAD = 16
ULTRAHLE_MAX_QUEUE = 128
def make_ultrahle_patch(patch_id: int) -> int:
    return u32((ULTRAHLE_OP_PATCH << 26) | (patch_id & 0xFFFF))

# GPR aliases (N64 o32)
_UH_V0, _UH_V1, _UH_A0, _UH_A1, _UH_A2, _UH_A3, _UH_SP, _UH_RA = 2, 3, 4, 5, 6, 7, 29, 31
OS_EVENT_SW1=0; OS_EVENT_SW2=1; OS_EVENT_CART=2; OS_EVENT_COUNTER=3
OS_EVENT_SP=4; OS_EVENT_SI=5; OS_EVENT_AI=6; OS_EVENT_VI=7; OS_EVENT_PI=8; OS_EVENT_DP=9
OS_EVENT_PRENMI=14; OS_EVENT_RETRACE=15  # UltraHLE uses RETRACE for osViSetEvent
OS_MESG_NOBLOCK=0; OS_MESG_BLOCK=1


class UltraHleOs:
    """UltraHLE os.c — threads, mesg queues, events, timers (PATCH-backed)."""
    __slots__ = (
        "core", "queues", "queue_by_addr", "queuenum",
        "event_mq", "event_msg", "fb_current", "fb_next",
        "threads", "thread_by_addr", "current_thread", "threadnum",
        "timers", "sptaskload", "time_lo", "time_hi",
        "cont_status", "cont_pad", "ai_freq", "ai_buf", "ai_len",
        "ismario", "iszelda", "bootloader", "block_pc", "pending_switch", "preempt_tid",
    )

    def __init__(self, core: "ACsN64Core"):
        self.core = core
        self.reset()

    def reset(self):
        self.queues: Dict[int, Dict[str, Any]] = {}
        self.queue_by_addr: Dict[int, int] = {}
        self.queuenum = 1
        self.event_mq: Dict[int, int] = {}
        self.event_msg: Dict[int, int] = {}
        self.fb_current = 0
        self.fb_next = 0
        self.threads: Dict[int, Dict[str, Any]] = {}
        self.thread_by_addr: Dict[int, int] = {}
        self.current_thread = 0
        self.threadnum = 1
        self.timers: Dict[int, Dict[str, Any]] = {}
        self.sptaskload = False
        self.time_lo = 0
        self.time_hi = 0
        self.cont_status = 0x0500
        self.cont_pad = 0
        self.ai_freq = 32000
        self.ai_buf = 0
        self.ai_len = 0
        self.ismario = 0
        self.iszelda = 0
        self.bootloader = 0
        self.block_pc = 0
        self.pending_switch = 0
        self.preempt_tid = 0
        # Boot context as thread 0 (idle/boot)
        self.threads[0] = {
            "id": 0, "memaddr": 0, "active": 1, "ready": 1, "pri": 0,
            "recvblock": 0, "sendblock": 0,
            "pc": 0, "next_pc": 4, "gpr": [0] * 32, "hi": 0, "lo": 0,
        }

    # compat alias used by older helpers
    @property
    def mq(self):
        return self.queue_by_addr

    @property
    def running_thread(self):
        return self.current_thread

    @running_thread.setter
    def running_thread(self, v):
        self.current_thread = v

    def _bus(self):
        return self.core.bus

    def _rd32(self, addr: int) -> int:
        return self._bus().read_u32(u32(addr))

    def _wr32(self, addr: int, val: int):
        self._bus().write_u32(u32(addr), u32(val))

    def _sp_arg(self, g, n: int) -> int:
        return self._rd32(u32(g[_UH_SP] + 0x10 + n * 4))

    def install_patch(self, vaddr: int, patch_id: int):
        self._wr32(vaddr, make_ultrahle_patch(patch_id))

    def _save_thread_cpu(self, tid: int):
        cpu = self.core.cpu
        t = self.threads.get(tid)
        if t is None:
            return
        t["pc"] = u32(cpu.pc)
        t["next_pc"] = u32(cpu.next_pc)
        t["gpr"] = list(cpu.gpr)
        t["hi"] = cpu.hi
        t["lo"] = cpu.lo

    def _load_thread_cpu(self, tid: int):
        cpu = self.core.cpu
        t = self.threads[tid]
        cpu.gpr = list(t["gpr"])
        cpu.gpr[0] = 0
        cpu.hi = t.get("hi", 0)
        cpu.lo = t.get("lo", 0)
        cpu.pc = u32(t["pc"])
        cpu.next_pc = u32(t["next_pc"])
        self.current_thread = tid

    def _find_ready_thread(self, prefer: int = 0) -> Optional[int]:
        best = None
        best_pri = -1
        start = prefer if prefer else self.current_thread
        for i in range(ULTRAHLE_MAX_THREAD * 2):
            tid = (start + 1 + i) & (ULTRAHLE_MAX_THREAD - 1)
            t = self.threads.get(tid)
            if not t or not t.get("ready"):
                continue
            pri = int(t.get("pri", 0))
            if pri > best_pri:
                best = tid
                best_pri = pri
        return best

    def switch_to(self, tid: int):
        if tid == self.current_thread:
            return
        if tid not in self.threads:
            return
        self._save_thread_cpu(self.current_thread)
        self._load_thread_cpu(tid)

    def schedule(self, prefer: int = 0) -> bool:
        """UltraHLE forcetaskswitch / os_switchcheck (simplified).

        Switch only when the current thread is not ready, or when another ready
        thread has strictly higher priority (preempt). Never demote a running
        high-priority thread to idle/boot just because schedule() was called.
        """
        cur = self.threads.get(self.current_thread)
        cur_ready = bool(cur is not None and cur.get("ready"))
        cur_pri = int(cur.get("pri", -1)) if cur_ready else -1
        t = self._find_ready_thread(prefer)
        pref_t = self.threads.get(prefer) if prefer else None
        if prefer and pref_t and pref_t.get("ready"):
            # Prefer started/unblocked thread when its priority wins or ties.
            if t is None or pref_t.get("pri", 0) >= self.threads.get(t, {}).get("pri", -1):
                t = prefer
        if t is not None and t != self.current_thread:
            t_pri = int(self.threads[t].get("pri", 0))
            if (not cur_ready) or t_pri > cur_pri:
                self.switch_to(t)
                return True
        return False

    def block_current(self, reason_q: int = 0, send: bool = False):
        """UltraHLE blocktask — mark not ready and switch away."""
        tid = self.current_thread
        t = self.threads.get(tid)
        if t is None:
            return
        t["ready"] = 0
        if send:
            t["sendblock"] = reason_q
        else:
            t["recvblock"] = reason_q
        # Rewind is handled by patch returning "block"; save after rewind via caller.
        self.schedule(0)

    def unblock_waiters(self, qid: int, recv: bool = True):
        # Mark ready only. If the waiter outranks the current thread, request a
        # deferred preempt so _h_PATCH can switch AFTER restoring the sender's RA
        # (immediate schedule mid-PATCH would corrupt the woken thread's PC).
        for tid, t in self.threads.items():
            if recv and t.get("recvblock") == qid:
                t["recvblock"] = 0
                t["ready"] = 1
                self._request_preempt(tid)
                return
            if (not recv) and t.get("sendblock") == qid:
                t["sendblock"] = 0
                t["ready"] = 1
                self._request_preempt(tid)
                return

    def _request_preempt(self, tid: int):
        t = self.threads.get(tid)
        if t is None or not t.get("ready"):
            return
        cur = self.threads.get(self.current_thread)
        cur_pri = int(cur.get("pri", -1)) if cur is not None else -1
        if int(t.get("pri", 0)) > cur_pri:
            self.preempt_tid = tid

    def maybe_preempt(self) -> bool:
        """Switch to a pending higher-priority thread if one was woken."""
        tid = self.preempt_tid
        self.preempt_tid = 0
        if tid and tid != self.current_thread:
            t = self.threads.get(tid)
            if t is not None and t.get("ready"):
                return self.schedule(tid)
        # Also pick any ready thread that outranks the current one.
        cur = self.threads.get(self.current_thread)
        cur_pri = int(cur.get("pri", -1)) if cur is not None else -1
        best = self._find_ready_thread()
        if best is not None and best != self.current_thread:
            if int(self.threads[best].get("pri", 0)) > cur_pri:
                return self.schedule(best)
        return False

    def yield_fair(self) -> bool:
        """Round-robin among ready non-idle threads so a mid-pri compute loop
        (e.g. SM64 audio) cannot starve lower-pri graphics for a whole frame."""
        cur = self.current_thread
        ready = [
            tid for tid, t in self.threads.items()
            if t.get("ready") and int(t.get("pri", 0)) > 0
        ]
        if len(ready) < 2:
            return False
        ready.sort()
        try:
            idx = ready.index(cur)
            nxt = ready[(idx + 1) % len(ready)]
        except ValueError:
            nxt = ready[0]
        if nxt != cur:
            self.switch_to(nxt)
            return True
        return False

    # ── queues (UltraHLE layout: id @+0, magic @+4, valid @+8, max @+16) ──
    def _queue_to_mem(self, qid: int):
        q = self.queues[qid]
        mq = q["memaddr"]
        self._wr32(mq + 0x00, qid)
        self._wr32(mq + 0x04, ULTRAHLE_MQ_MAGIC)
        self._wr32(mq + 0x08, q["num"])
        self._wr32(mq + 0x10, q["size"])

    def os_create_mesg_queue(self, mq: int, msg: int, count: int):
        mq = u32(mq); msg = u32(msg); count = max(0, sign32(count))
        # Reuse dead id or allocate
        qid = self.queue_by_addr.get(mq)
        if not qid:
            qid = self.queuenum
            self.queuenum = min(self.queuenum + 1, ULTRAHLE_MAX_QUEUE - 1)
            if qid <= 0:
                qid = 1
        self.queues[qid] = {
            "memaddr": mq, "msg": msg, "size": max(1, count), "num": 0, "pos": 0,
            "data": [0] * max(1, count),
        }
        self.queue_by_addr[mq] = qid
        self._queue_to_mem(qid)

    def _qid_from_mq(self, mq: int) -> int:
        mq = u32(mq)
        qid = self._rd32(mq)
        if qid in self.queues and self.queues[qid]["memaddr"] == mq:
            return qid
        if mq in self.queue_by_addr:
            return self.queue_by_addr[mq]
        # Uninitialized: treat as empty create
        return 0

    def os_send_mesg(self, mq: int, mesg: int, block: int) -> int:
        qid = self._qid_from_mq(mq)
        if not qid or qid not in self.queues:
            return 0
        q = self.queues[qid]
        if q["num"] >= q["size"]:
            if block == OS_MESG_NOBLOCK or block == -1:
                # Drop oldest so VI/SP event streams never permanently stall.
                if q["size"] > 0:
                    q["num"] -= 1
                else:
                    return -1
            else:
                self.block_pc = 1
                cur = self.threads.get(self.current_thread)
                if cur is not None:
                    cur["sendblock"] = qid
                return 1
        q["data"][q["pos"]] = u32(mesg)
        q["num"] += 1
        q["pos"] = (q["pos"] + 1) % q["size"]
        self._queue_to_mem(qid)
        self.unblock_waiters(qid, recv=True)
        return 0

    def os_recv_mesg(self, mq: int, msg_ptr: int, block: int) -> int:
        qid = self._qid_from_mq(mq)
        if not qid or qid not in self.queues:
            if block == OS_MESG_NOBLOCK:
                return -1
            self.block_pc = 1
            return 1
        q = self.queues[qid]
        if q["num"] <= 0:
            if block == OS_MESG_NOBLOCK:
                return -1
            self.block_pc = 1
            cur = self.threads.get(self.current_thread)
            if cur is not None:
                cur["recvblock"] = qid
            return 1
        pos = q["pos"] - q["num"]
        if pos < 0:
            pos += q["size"]
        mesg = q["data"][pos]
        q["num"] -= 1
        self._queue_to_mem(qid)
        if msg_ptr:
            self._wr32(msg_ptr, u32(mesg))
        self.unblock_waiters(qid, recv=False)
        return 0

    def os_set_event_mesg(self, event: int, mq: int, mesg: int):
        event &= 0xFF
        self.event_mq[event] = u32(mq)
        self.event_msg[event] = u32(mesg)

    def os_event(self, event: int):
        mq = self.event_mq.get(event)
        if mq is not None:
            self.os_send_mesg(mq, self.event_msg.get(event, 0), OS_MESG_NOBLOCK)

    def tick_time(self, cycles: int = 1):
        self.time_lo = u32(self.time_lo + cycles)
        if self.time_lo < (cycles & MASK_32):
            self.time_hi = u32(self.time_hi + 1)
        self._fire_timers(u32(self.core.cpu.cp0[CP0_COUNT]))

    def _fire_timers(self, count: int):
        """Deliver osSetTimer messages when COUNT reaches expiry."""
        count = u32(count)
        for t in self.timers.values():
            if not t.get("active"):
                continue
            expire = u32(t.get("expire", 0))
            # Not expired yet if (count - expire) is still a large unsigned (count < expire).
            if u32(count - expire) > 0x7FFFFFFF:
                continue
            mq = t.get("mq")
            if mq:
                self.os_send_mesg(mq, t.get("msg", 0), OS_MESG_NOBLOCK)
            iv = u32(t.get("interval", 0))
            if iv:
                t["expire"] = u32(count + iv)
            else:
                t["active"] = False

    def virt_to_phys(self, addr: int) -> int:
        return self._bus().v_to_p(u32(addr)) & 0x1FFFFFFF

    def phys_to_virt(self, addr: int) -> int:
        return u32(0x80000000 | (u32(addr) & 0x1FFFFFFF))

    def create_thread(self, m_thread: int, tid: int, entry: int, arg: int, stack: int, pri: int):
        m_thread = u32(m_thread)
        tid = u32(tid) & 0xFF
        if tid <= 0 or tid >= ULTRAHLE_MAX_THREAD or (tid in self.threads and self.threads[tid].get("active")):
            for i in range(1, ULTRAHLE_MAX_THREAD):
                if i not in self.threads or not self.threads[i].get("active"):
                    tid = i
                    break
        gpr = [0] * 32
        gpr[4] = u64(arg)
        gpr[29] = u64(u32(stack) - 8)
        gpr[31] = u64(ULTRAHLE_THREAD_RA)
        self.threads[tid] = {
            "id": tid, "memaddr": m_thread, "active": 1, "ready": 0,
            "pri": int(pri) * 10, "recvblock": 0, "sendblock": 0,
            "pc": u32(entry), "next_pc": u32(entry + 4),
            "gpr": gpr, "hi": 0, "lo": 0,
        }
        self.thread_by_addr[m_thread] = tid
        self._wr32(m_thread, tid)
        if tid >= self.threadnum:
            self.threadnum = tid + 1

    def start_thread(self, m_thread: int):
        m_thread = u32(m_thread)
        tid = self._rd32(m_thread)
        if tid not in self.threads:
            tid = self.thread_by_addr.get(m_thread, tid)
        t = self.threads.get(tid)
        if t is None:
            return
        t["ready"] = 1
        # Save current so it resumes at RA (after this PATCH returns).
        cpu = self.core.cpu
        cur = self.threads.get(self.current_thread)
        ra = u32(cpu.gpr[_UH_RA])
        cpu.pc = ra
        cpu.next_pc = u32(ra + 4)
        if cur is not None:
            cur["pc"] = ra
            cur["next_pc"] = u32(ra + 4)
            cur["gpr"] = list(cpu.gpr)
            cur["hi"] = cpu.hi
            cur["lo"] = cpu.lo
        self.pending_switch = tid
        # Prefer the started thread if its priority wins (do not re-save current).
        self.schedule(tid)

    def stop_current_thread(self):
        tid = self.current_thread
        t = self.threads.get(tid)
        if t is not None:
            t["active"] = 0
            t["ready"] = 0
        self.schedule(0)


# Patch routines — indices match UltraHLE PATCH.C patchtable[]
def _uh_skip(hle, cpu, g): pass
def _uh_osskip(hle, cpu, g): pass
def _uh_osskip0(hle, cpu, g): g[_UH_V0] = 0
def _uh_dabort(hle, cpu, g): pass

def _uh_ddivu(hle, cpu, g):
    a = (u64(g[_UH_A0]) << 32) | u64(g[_UH_A1] & MASK_32)
    b = (u64(g[_UH_A2]) << 32) | u64(g[_UH_A3] & MASK_32)
    if b == 0: r = 0
    else: r = a // b
    g[_UH_V0] = u64(r >> 32); g[_UH_V1] = u64(r & MASK_32)

def _uh_dmultu(hle, cpu, g):
    a = (u64(g[_UH_A0]) << 32) | u64(g[_UH_A1] & MASK_32)
    b = (u64(g[_UH_A2]) << 32) | u64(g[_UH_A3] & MASK_32)
    r = a * b
    g[_UH_V0] = u64(r >> 32); g[_UH_V1] = u64(r & MASK_32)

def _uh_drem(hle, cpu, g):
    a = (u64(g[_UH_A0]) << 32) | u64(g[_UH_A1] & MASK_32)
    b = (u64(g[_UH_A2]) << 32) | u64(g[_UH_A3] & MASK_32)
    r = 0 if b == 0 else a % b
    g[_UH_V0] = u64(r >> 32); g[_UH_V1] = u64(r & MASK_32)

def _uh_ddiv(hle, cpu, g):
    a = sign64((u64(g[_UH_A0]) << 32) | u64(g[_UH_A1] & MASK_32))
    b = sign64((u64(g[_UH_A2]) << 32) | u64(g[_UH_A3] & MASK_32))
    r = 0 if b == 0 else a // b
    g[_UH_V0] = u64(r >> 32); g[_UH_V1] = u64(r & MASK_32)

def _uh_osCreateThread(hle, cpu, g):
    hle.create_thread(
        u32(g[_UH_A0]), u32(g[_UH_A1]), u32(g[_UH_A2]), u32(g[_UH_A3]),
        hle._sp_arg(g, 0), hle._sp_arg(g, 1),
    )

def _uh_osStartThread(hle, cpu, g):
    hle.start_thread(u32(g[_UH_A0]))
    return "switched"

def _uh_osStopCurrentThread(hle, cpu, g):
    hle.stop_current_thread()
    return "switched"

def _uh_osSetThreadPri(hle, cpu, g):
    m_thr = u32(g[_UH_A0])
    pri = u32(g[_UH_A1])
    tid = hle.current_thread if m_thr == 0 else hle._rd32(m_thr)
    t = hle.threads.get(tid)
    if t is not None:
        t["pri"] = int(pri) * 10
        # Resume caller at RA after any forced switch (not mid-PATCH).
        ra = u32(g[_UH_RA])
        cpu.pc = ra
        cpu.next_pc = u32(ra + 4)
        hle.schedule(tid)
        return "switched"

def _uh_osPiStartDma(hle, cpu, g):
    # A0=mb, A1=pri, A2=direction, A3=devAddr; stack: vAddr, nBytes, mq
    direction = u32(g[_UH_A2])
    dev = u32(g[_UH_A3])
    vaddr = hle._sp_arg(g, 0)
    nbytes = hle._sp_arg(g, 1)
    mq = hle._sp_arg(g, 2)
    bus = hle._bus()
    # cart offset is often a raw cart address; accept both 0x1xxx_xxxx and bare offsets
    cart = u32(dev)
    if cart < 0x10000000:
        cart = u32(0x10000000 + (cart & 0x0FFFFFFF))
    bus.regs[PI_DRAM_ADDR] = hle.virt_to_phys(vaddr) & 0x00FFFFFF
    bus.regs[PI_CART_ADDR] = cart
    if direction == 0:  # cart -> rdram
        bus.regs[PI_WR_LEN] = max(0, int(nbytes) - 1)
        bus.regs[PI_RD_LEN] = 0
        hle.core.trigger_pi_dma()
    else:
        bus.regs[PI_RD_LEN] = max(0, int(nbytes) - 1)
        bus.regs[PI_WR_LEN] = 0
        hle.core.trigger_pi_dma()
    # UltraHLE: notify requester queue immediately, then PI event.
    if mq:
        hle.os_send_mesg(mq, 0, -1)
    hle.os_event(OS_EVENT_PI)
    g[_UH_V0] = 0

def _uh_osEPiStartDma(hle, cpu, g):
    # A0=OSPiHandle*, A1=OSIoMesg* — DMA from mesg fields, notify retQueue.
    mb = u32(g[_UH_A1])
    if not mb:
        g[_UH_V0] = -1
        return
    mq = hle._rd32(mb + 4)
    vaddr = hle._rd32(mb + 8)
    dev = hle._rd32(mb + 12)
    nbytes = hle._rd32(mb + 16)
    # OS_READ=0 (cart→RDRAM), OS_WRITE=1
    direction = hle._rd32(mb) & 0xFF
    bus = hle._bus()
    cart = u32(dev)
    if cart < 0x10000000:
        cart = u32(0x10000000 + (cart & 0x0FFFFFFF))
    bus.regs[PI_DRAM_ADDR] = hle.virt_to_phys(vaddr) & 0x00FFFFFF
    bus.regs[PI_CART_ADDR] = cart
    if direction == 0:
        bus.regs[PI_WR_LEN] = max(0, int(nbytes) - 1)
        bus.regs[PI_RD_LEN] = 0
    else:
        bus.regs[PI_RD_LEN] = max(0, int(nbytes) - 1)
        bus.regs[PI_WR_LEN] = 0
    hle.core.trigger_pi_dma()
    if mq:
        hle.os_send_mesg(mq, mb, -1)
    hle.os_event(OS_EVENT_PI)
    g[_UH_V0] = 0

def _uh_osCreateMesgQueue(hle, cpu, g):
    hle.os_create_mesg_queue(g[_UH_A0], g[_UH_A1], g[_UH_A2])

def _uh_osRecvMesg(hle, cpu, g):
    hle.block_pc = 0
    rc = hle.os_recv_mesg(g[_UH_A0], g[_UH_A1], g[_UH_A2])
    if hle.block_pc:
        # UltraHLE blocktask: mark not-ready FIRST, then yield to another thread.
        # Do NOT inject os_event here — that can fill the wait queue and clear
        # recvblock, after which setting ready=0 leaves the thread wedged.
        cur = hle.threads.get(hle.current_thread)
        patch_pc = u32(getattr(cpu, "_patch_pc", cpu.pc))
        # Rewind onto PATCH before schedule/_save so we don't resume mid-native body.
        cpu.pc = patch_pc
        cpu.next_pc = u32(patch_pc + 4)
        if cur is not None:
            cur["ready"] = 0
            cur["pc"] = patch_pc
            cur["next_pc"] = u32(patch_pc + 4)
            cur["gpr"] = list(cpu.gpr)
            cur["hi"] = cpu.hi
            cur["lo"] = cpu.lo
        g[_UH_V0] = 0
        cpu.gpr[_UH_V0] = 0
        cpu.cp0[CP0_COUNT] = u32(cpu.cp0[CP0_COUNT] + 64)
        switched = hle.schedule(0)
        if switched:
            return "switched"
        return "block"
    g[_UH_V0] = sx32_to_64(rc)
    return None

def _uh_osSendMesg(hle, cpu, g):
    g[_UH_V0] = sx32_to_64(hle.os_send_mesg(g[_UH_A0], g[_UH_A1], g[_UH_A2]))

def _uh_osSetEventMessage(hle, cpu, g):
    hle.os_set_event_mesg(g[_UH_A0], g[_UH_A1], g[_UH_A2])

def _uh_osViSetEvent(hle, cpu, g):
    # UltraHLE maps this to OS_EVENT_RETRACE only (sync.c). Binding VI as well
    # double-posts on titles that share a size-1 mq with DMA/audio.
    hle.os_set_event_mesg(OS_EVENT_RETRACE, g[_UH_A0], g[_UH_A1])

def _uh_osGetTime(hle, cpu, g):
    hle.tick_time(cpu.cp0[CP0_COUNT] & MASK_32)
    g[_UH_V0] = u64(hle.time_hi)
    g[_UH_V1] = u64(hle.time_lo)

def _uh_osGetCount(hle, cpu, g):
    g[_UH_V0] = sx32_to_64(cpu.cp0[CP0_COUNT])

def _uh_osViGetCurrentFrameBuffer(hle, cpu, g):
    g[_UH_V0] = u64(hle.fb_current or hle._bus().regs.get(VI_ORIGIN, 0))

def _uh_osViSwapBuffer(hle, cpu, g):
    hle.fb_next = u32(g[_UH_A0])
    hle.fb_current = hle.fb_next
    # VI_ORIGIN is a physical DRAM address (24-bit); keep virt in fb_current for OS.
    hle._bus().regs[VI_ORIGIN] = hle.virt_to_phys(hle.fb_current) & 0x00FFFFFF
    hle.core._vi_origin_set = True
    hle.core.render_vi()
    # Real osViSwapBuffer does not post a mesg; VI/RETRACE interrupt does.

def _uh_osVirtualToPhysical(hle, cpu, g):
    g[_UH_V0] = u64(hle.virt_to_phys(g[_UH_A0]))

def _uh_osPhysicalToVirtual(hle, cpu, g):
    g[_UH_V0] = u64(hle.phys_to_virt(g[_UH_A0]))

def _uh_osSpTaskStartGo(hle, cpu, g):
    task = u32(g[_UH_A0])
    if not hle.sptaskload:
        if task:
            ttype = hle._rd32(task)
            put_be32(hle.core.rsp_dmem, 0xFC0, ttype)
            hle.core.last_os_task = task
        hle.core.process_rsp()
    elif task:
        hle.core.last_os_task = task
    hle.sptaskload = False
    # UltraHLE retires RSP/RDP immediately — notify event subscribers.
    hle.os_event(OS_EVENT_SP)
    hle.os_event(OS_EVENT_DP)

def _uh_osSpTaskLoad(hle, cpu, g):
    task = u32(g[_UH_A0])
    if task:
        ttype = hle._rd32(task)
        put_be32(hle.core.rsp_dmem, 0xFC0, ttype)
        hle.core.last_os_task = task
    hle.core.process_rsp()
    hle.sptaskload = True
    # Completion events fired by osSpTaskStartGo.

def _uh_osSpTaskYield(hle, cpu, g): g[_UH_V0] = 0
def _uh_osSpTaskYielded(hle, cpu, g): g[_UH_V0] = 0

def _uh_osMapTLB(hle, cpu, g):
    # A0=index, A1=pmask, A2=vaddr, A3=evenpaddr; stack: oddpaddr, asid
    idx = u32(g[_UH_A0]) & 0x1F
    pmask = u32(g[_UH_A1])
    vaddr = u32(g[_UH_A2])
    even_p = u32(g[_UH_A3])
    odd_p = hle._sp_arg(g, 0)
    asid = hle._sp_arg(g, 1) & 0xFF
    cpu.cp0[CP0_INDEX] = idx
    cpu.cp0[CP0_PAGEMASK] = pmask
    cpu.cp0[CP0_ENTRYHI] = (vaddr & 0xFFFFE000) | asid
    cpu.cp0[CP0_ENTRYLO0] = ((even_p >> 12) << 6) | 0x06  # V|D
    cpu.cp0[CP0_ENTRYLO1] = ((odd_p >> 12) << 6) | 0x06
    cpu._write_tlb_entry(idx)

def _uh_osContInit(hle, cpu, g):
    # Write status pattern into statusdata if provided
    status = u32(g[_UH_A1])
    if status:
        hle._wr32(status, 0x05000200)
    g[_UH_V0] = 0

def _uh_osContStartReadData(hle, cpu, g):
    hle.os_event(OS_EVENT_SI)
    g[_UH_V0] = 0

def _uh_osContGetReadData(hle, cpu, g):
    pad = u32(g[_UH_A0])
    if not pad:
        return
    bus = hle._bus()
    # OSContPad: u16 button, s8 stick_x, s8 stick_y, u8 errno (6 bytes × 4).
    for i in range(4):
        base = pad + i * 6
        btn = (hle.cont_pad & 0xFFFF) if i == 0 else 0
        bus.write_u16(base, btn)
        bus.write_u8(base + 2, 0)
        bus.write_u8(base + 3, 0)
        bus.write_u8(base + 4, 0)

def _uh_osContStartQuery(hle, cpu, g):
    hle.os_event(OS_EVENT_SI)
    g[_UH_V0] = 0

def _uh_osContGetQuery(hle, cpu, g):
    status = u32(g[_UH_A0])
    if status:
        hle._wr32(status, 0x05000200)

def _uh_osAiSetNextBuffer(hle, cpu, g):
    hle.ai_buf = u32(g[_UH_A0]); hle.ai_len = u32(g[_UH_A1])
    hle._bus().regs[AI_DRAM_ADDR] = hle.ai_buf & 0x00FFFFFF
    hle._bus().regs[AI_LEN] = hle.ai_len
    hle.core.process_audio()
    # Audio threads block on AI completion — post the event so commercial titles continue.
    hle.os_event(OS_EVENT_AI)
    g[_UH_V0] = 0

def _uh_osAiGetLength(hle, cpu, g):
    g[_UH_V0] = u64(hle._bus().regs.get(AI_LEN, 0))

def _uh_osAiSetFrequency(hle, cpu, g):
    hle.ai_freq = u32(g[_UH_A0]) or 32000
    g[_UH_V0] = u64(hle.ai_freq)

def _uh_osSetTimer(hle, cpu, g):
    # osSetTimer(OSTimer*, OSTime countdown, OSTime interval, OSMesgQueue*, OSMesg)
    # o32: A0=timer, A2:A3=countdown, stack=interval(hi,lo), mq, msg.
    timer = u32(g[_UH_A0])
    countdown = u32(g[_UH_A3])  # low half is enough for HLE pacing
    interval = u32(hle._sp_arg(g, 1))
    mq = hle._sp_arg(g, 2)
    msg = hle._sp_arg(g, 3)
    now = u32(cpu.cp0[CP0_COUNT])
    delay = countdown if countdown else 1
    hle.timers[timer] = {
        "active": True,
        "expire": u32(now + delay),
        "interval": interval,
        "mq": mq,
        "msg": msg,
    }
    g[_UH_V0] = 0

def _uh_osStopTimer(hle, cpu, g):
    timer = u32(g[_UH_A0])
    if timer in hle.timers:
        hle.timers[timer]["active"] = False

def _uh_sinf(hle, cpu, g):
    x = bits_to_f32(cpu.fpr[12] & MASK_32)
    cpu.fpr[0] = u64((cpu.fpr[0] & 0xFFFFFFFF00000000) | f32_to_bits(math.sin(x)))

def _uh_cosf(hle, cpu, g):
    x = bits_to_f32(cpu.fpr[12] & MASK_32)
    cpu.fpr[0] = u64((cpu.fpr[0] & 0xFFFFFFFF00000000) | f32_to_bits(math.cos(x)))

def _uh_osInvalICache(hle, cpu, g): pass

def _uh_readdma(hle, cpu, g):
    # Zelda-style cart→RDRAM helper: A0=cart, A1=dram, A2=nbytes
    bus = hle._bus()
    cart = u32(g[_UH_A0])
    if cart < 0x10000000:
        cart = u32(0x10000000 + (cart & 0x0FFFFFFF))
    bus.regs[PI_CART_ADDR] = cart
    bus.regs[PI_DRAM_ADDR] = hle.virt_to_phys(g[_UH_A1]) & 0x00FFFFFF
    bus.regs[PI_WR_LEN] = max(0, u32(g[_UH_A2]) - 1)
    bus.regs[PI_RD_LEN] = 0
    hle.core.trigger_pi_dma()
    hle.os_event(OS_EVENT_PI)

def _uh_readdma2(hle, cpu, g):
    # Patched to osPiStartDma(0,0,0,A0,A1,A2,0)
    bus = hle._bus()
    bus.regs[PI_CART_ADDR] = u32(g[_UH_A0])
    bus.regs[PI_DRAM_ADDR] = hle.virt_to_phys(g[_UH_A1]) & 0x00FFFFFF
    bus.regs[PI_WR_LEN] = max(0, u32(g[_UH_A2]) - 1)
    hle.core.trigger_pi_dma()

def _uh_zeldacont(hle, cpu, g): hle.os_event(OS_EVENT_SI)
def _uh_zeldagrabscreen(hle, cpu, g): pass
def _uh_banjojalr(hle, cpu, g):
    # Fall through to next instruction (UltraHLE branches to pc+4)
    cpu.pc = u32(cpu.pc)  # already at delay/next after execute preamble
    # Keep sequential fetch: undo RA return by staying at next_pc path.
    # Caller already set pc=RA; Banjo patch instead continues. Restore:
    pass  # handled specially in _h_PATCH

def _uh_long2double(hle, cpu, g):
    a = sign64((u64(g[_UH_A0]) << 32) | u64(g[_UH_A1] & MASK_32))
    cpu.fpr[0] = f64_to_bits(float(a))

def _uh_long2single(hle, cpu, g):
    a = sign64((u64(g[_UH_A0]) << 32) | u64(g[_UH_A1] & MASK_32))
    cpu.fpr[0] = u64((cpu.fpr[0] & 0xFFFFFFFF00000000) | f32_to_bits(float(a)))

def _uh_double2long(hle, cpu, g):
    d = bits_to_f64(cpu.fpr[12])
    a = int(d) if math.isfinite(d) else 0
    g[_UH_V1] = u64(a & MASK_32); g[_UH_V0] = u64((a >> 32) & MASK_32)

def _uh_single2long(hle, cpu, g):
    f = bits_to_f32(cpu.fpr[12] & MASK_32)
    a = int(f) if math.isfinite(f) else 0
    g[_UH_V1] = u64(a & MASK_32); g[_UH_V0] = u64((a >> 32) & MASK_32)

def _uh_golden1(hle, cpu, g):
    x = random.randint(0, 0xFFFFFFFF)
    x = u32((x << 8) | (x >> 24))
    g[_UH_V0] = sx32_to_64(x)

def _uh_createvimanager(hle, cpu, g):
    # A0 is priority (e.g. SM64 passes 0xFE), not a mesg queue. Real libultra
    # spins up a VI manager thread; with HLE osViSetEvent we already deliver
    # retrace msgs, so this is a no-op (do not overwrite event MQ with priority).
    g[_UH_V0] = 0

def _uh_memcpy(hle, cpu, g):
    dst, src, count = u32(g[_UH_A0]), u32(g[_UH_A1]), u32(g[_UH_A2]) >> 2
    bus = hle._bus()
    for _ in range(count):
        bus.write_u32(dst, bus.read_u32(src))
        dst = u32(dst + 4); src = u32(src + 4)

def _uh_osEepromProbe(hle, cpu, g):
    # osEepromProbe(OSMesgQueue*) → EEPROM_TYPE_4K/16K or 0
    sm = hle.core.save_mgr
    typ = sm.eeprom_probe()
    hle.os_event(OS_EVENT_SI)
    g[_UH_V0] = typ

def _uh_osEepromRead(hle, cpu, g):
    # osEepromRead(mq, address, buffer) — 8 bytes at block `address`
    sm = hle.core.save_mgr
    block = u32(g[_UH_A1]) & 0xFF
    buf = u32(g[_UH_A2])
    tmp = bytearray(EEPROM_BLOCK)
    rc = sm.eeprom_read_block(block, tmp)
    if rc == 0 and buf:
        bus = hle._bus()
        for i in range(EEPROM_BLOCK):
            bus.write_u8(u32(buf + i), tmp[i])
    hle.os_event(OS_EVENT_SI)
    g[_UH_V0] = 0 if rc == 0 else -1

def _uh_osEepromWrite(hle, cpu, g):
    # osEepromWrite(mq, address, buffer)
    sm = hle.core.save_mgr
    block = u32(g[_UH_A1]) & 0xFF
    buf = u32(g[_UH_A2])
    tmp = bytearray(EEPROM_BLOCK)
    if buf:
        bus = hle._bus()
        for i in range(EEPROM_BLOCK):
            tmp[i] = bus.read_u8(u32(buf + i)) & 0xFF
    rc = sm.eeprom_write_block(block, tmp)
    hle.os_event(OS_EVENT_SI)
    g[_UH_V0] = 0 if rc == 0 else -1

def _uh_osEepromLongRead(hle, cpu, g):
    # osEepromLongRead(mq, address, buffer, nbytes) — nbytes in A3 (o32)
    sm = hle.core.save_mgr
    block = u32(g[_UH_A1]) & 0xFF
    buf = u32(g[_UH_A2])
    nbytes = u32(g[_UH_A3])
    rc = sm.eeprom_long_read(block, nbytes, hle._bus(), buf) if buf else -1
    hle.os_event(OS_EVENT_SI)
    g[_UH_V0] = 0 if rc == 0 else -1

def _uh_osEepromLongWrite(hle, cpu, g):
    # osEepromLongWrite(mq, address, buffer, nbytes) — nbytes in A3 (o32)
    sm = hle.core.save_mgr
    block = u32(g[_UH_A1]) & 0xFF
    buf = u32(g[_UH_A2])
    nbytes = u32(g[_UH_A3])
    rc = sm.eeprom_long_write(block, nbytes, hle._bus(), buf) if buf else -1
    hle.os_event(OS_EVENT_SI)
    g[_UH_V0] = 0 if rc == 0 else -1

# Index-aligned with UltraHLE PATCH.C patchtable[] (+ cathle EEPROM 57..61)
ULTRAHLE_PATCH_TABLE: Dict[int, Callable] = {
    1: _uh_skip, 2: _uh_osskip, 3: _uh_ddivu, 4: _uh_dmultu,
    5: _uh_drem, 6: _uh_ddiv, 7: _uh_drem, 8: _uh_osskip0, 9: _uh_dabort,
    10: _uh_osCreateThread, 11: _uh_osStartThread, 12: _uh_osPiStartDma,
    13: _uh_osCreateMesgQueue, 14: _uh_osRecvMesg, 15: _uh_osSendMesg,
    16: _uh_osSetEventMessage, 17: _uh_osViSetEvent, 18: _uh_osSetThreadPri,
    19: _uh_osGetTime, 20: _uh_osViGetCurrentFrameBuffer, 21: _uh_osVirtualToPhysical,
    22: _uh_osSpTaskStartGo, 23: _uh_osViSwapBuffer, 24: _uh_osMapTLB,
    25: _uh_osContInit, 26: _uh_osContStartReadData, 27: _uh_osContGetReadData,
    28: _uh_osStopCurrentThread, 29: _uh_osPhysicalToVirtual,
    30: _uh_osAiSetNextBuffer, 31: _uh_osAiGetLength, 32: _uh_osAiSetFrequency,
    33: _uh_osSetTimer, 34: _uh_osStopTimer, 35: _uh_sinf, 36: _uh_cosf,
    37: _uh_osEPiStartDma, 38: _uh_osInvalICache, 39: _uh_osSpTaskLoad,
    40: _uh_readdma, 41: _uh_readdma2, 42: _uh_osContStartQuery, 43: _uh_osContGetQuery,
    44: _uh_zeldacont, 45: _uh_zeldagrabscreen, 46: _uh_osSpTaskYield,
    47: _uh_osSpTaskYielded, 48: _uh_osGetCount, 49: _uh_banjojalr,
    50: _uh_long2double, 51: _uh_long2single, 52: _uh_double2long, 53: _uh_single2long,
    54: _uh_golden1, 55: _uh_createvimanager, 56: _uh_memcpy,
    57: _uh_osEepromProbe, 58: _uh_osEepromRead, 59: _uh_osEepromWrite,
    60: _uh_osEepromLongRead, 61: _uh_osEepromLongWrite,
}
ULTRAHLE_PATCH_NAMES = {
    1: "skip", 2: "osskip", 3: "__ull_div", 4: "__ll_mul", 5: "__ull_rem",
    6: "__ll_div", 7: "__ll_rem", 8: "osskip0", 9: "dabort",
    10: "osCreateThread", 11: "osStartThread", 12: "osPiStartDma",
    13: "osCreateMesgQueue", 14: "osRecvMesg", 15: "osSendMesg",
    16: "osSetEventMesg", 17: "osViSetEvent", 18: "osSetThreadPri",
    19: "osGetTime", 20: "osViGetCurrentFramebuffer", 21: "osVirtualToPhysical",
    22: "osSpTaskStartGo", 23: "osViSwapBuffer", 24: "osMapTLB",
    25: "osContInit", 26: "osContStartReadData", 27: "osContGetReadData",
    28: "osStopCurrentThread", 29: "osPhysicalToVirtual",
    30: "osAiSetNextBuffer", 31: "osAiGetLength", 32: "osAiSetFrequency",
    33: "osSetTimer", 34: "osStopTimer", 35: "sinf", 36: "cosf",
    37: "osEPiStartDma", 38: "osInvalICache", 39: "osSpTaskLoad",
    40: "readdma", 41: "readdma2", 42: "osContStartQuery", 43: "osContGetQuery",
    44: "zeldacont", 45: "zeldagrabscreen", 46: "osSpTaskYield",
    47: "osSpTaskYielded", 48: "osGetCount", 49: "banjojalr",
    50: "long2double", 51: "long2single", 52: "double2long", 53: "single2long",
    54: "golden1", 55: "createViManager", 56: "memcpy",
    57: "osEepromProbe", 58: "osEepromRead", 59: "osEepromWrite",
    60: "osEepromLongRead", 61: "osEepromLongWrite",
}


# AUTOGEN: UltraHLE oscall/ospatch/ini (emu-russia/UltraHLE)
ULTRAHLE_OSCALL: List[Tuple] = [
  ((0x40024002,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x40008200,1,'__osGetCause  #1'),
  ((0x40024002,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x4000B200,1,'__osGetCompare  #1'),
  ((0x40024002,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x40006A00,1,'__osGetConfig  #1'),
  ((0x40024002,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x4000A200,48,'osGetCount #48'),
  ((0x44424442,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x44401200,1,'__osGetFpcCsr  #1'),
  ((0x40024002,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x40008A00,1,'__osGetSR #1'),
  ((0x40024002,0x30423042,0x3C083C08,0x25082508,0x8D098D09,0x24012401,0x01210121,0x31083108),0x000028AA,0x44E69EF4,2,'osGetIntMask  #2'),
  ((0x40024002,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x4000BA00,1,'__osGetTLBASID  #1'),
  ((0x40844084,0x00000000,0x42004200,0x00000000,0x00000000,0x00000000,0x40024002,0x03E003E0),0x00000000,0x4284D1C5,1,'__osGetTLBHi  #1'),
  ((0x40844084,0x00000000,0x42004200,0x00000000,0x00000000,0x00000000,0x40024002,0x03E003E0),0x00000000,0x428491C5,1,'__osGetTLBLo0  #1'),
  ((0x40844084,0x00000000,0x42004200,0x00000000,0x00000000,0x00000000,0x40024002,0x03E003E0),0x00000000,0x428499C5,1,'__osGetTLBLo1  #1'),
  ((0x40844084,0x00000000,0x42004200,0x00000000,0x00000000,0x00000000,0x40024002,0x03E003E0),0x00000000,0x4284A9C5,1,'__osGetTLBPageMask  #1'),
  ((0x18A018A0,0x00000000,0x240B240B,0x00AB00AB,0x10201020,0x00000000,0x00800080,0x00850085),0x00003A15,0x86C122C7,1,'osInvalDCache #1'),
  ((0x18A018A0,0x00000000,0x240B240B,0x00AB00AB,0x10201020,0x00000000,0x00800080,0x00850085),0x00001A15,0xFCC122C7,38,'osInvalICache #38'),
  ((0x40084008,0x24012401,0x01010101,0x40894089,0x31023102,0x00000000,0x03E003E0,0x00000000),0x00000012,0x0081B12C,1,'__osDisableInt #1'),
  ((0x40084008,0x01040104,0x40884088,0x00000000,0x00000000,0x03E003E0,0x00000000,0x00000000),0x00000000,0x06843070,1,'__osRestoreInt #1'),
  ((0x40084008,0x40844084,0x40854085,0x8FA98FA9,0x24012401,0x11211121,0x240C240C,0x240A240A),0x000035F0,0x5DB45780,24,'osMapTLB #24'),
  ((0x400C400C,0x31823182,0x3C083C08,0x25082508,0x8D0B8D0B,0x24012401,0x01610161,0x31083108),0x0000A8AA,0xAE358CFC,2,'osSetIntMask #2'),
  ((0x40844084,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x40868200,1,'__osSetCause  #1'),
  ((0x40844084,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x4086B200,1,'__osSetCompare #1'),
  ((0x40844084,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x40866A00,1,'__osSetConfig  #1'),
  ((0x40844084,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x4086A200,1,'__osSetCount  #1'),
  ((0x44424442,0x44C444C4,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x00863700,1,'__osSetFpcCsr #1'),
  ((0x40844084,0x00000000,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x40845710,1,'__osSetSR  #1'),
  ((0x40844084,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x4086BA00,2,'osSetTLBASID  #2'),
  ((0x40084008,0x40844084,0x3C093C09,0x40894089,0x40804080,0x40804080,0x00000000,0x42004200),0x00000000,0x5AC36802,2,'osUnmapTLB  #2'),
  ((0x40084008,0x24092409,0x3C0A3C0A,0x408A408A,0x40804080,0x40804080,0x40894089,0x00000000),0x00000802,0x484FD806,2,'osUnmapTLBAll  #2'),
  ((0x18A018A0,0x00000000,0x240B240B,0x00AB00AB,0x10201020,0x00000000,0x00800080,0x00850085),0x00001A15,0xCCC122C7,2,'osWritebackDCache #2'),
  ((0x3C083C08,0x240A240A,0x010A010A,0x25292529,0xBD01BD01,0x01090109,0x14201420,0x25082508),0x000000CA,0x000E9F38,1,'osWritebackDCacheAll #1'),
  ((0x40084008,0x24092409,0x40894089,0x40804080,0x240A240A,0x3C093C09,0x40894089,0x3C093C09),0x00000812,0x4ACCA206,2,'osMapTLBRdb #2'),
  ((0x27BD27BD,0xAFBFAFBF,0x00000000,0xAFA4AFA4,0x8FAE8FAE,0xAFA2AFA2,0x8DCF8DCF,0x11E011E0),0x00001A81,0xEE2EC003,1,'__osAtomicDec  #1'),
  ((0x3C0E3C0E,0x3C0F3C0F,0x25CE25CE,0x25EF25EF,0xAC8EAC8E,0xAC8FAC8F,0xAC80AC80,0xAC80AC80),0x0000000C,0x001D0124,13,'osCreateMesgQueue #13'),
  ((0x27BD27BD,0xAFA4AFA4,0xAFA5AFA5,0x8FAE8FAE,0x8FAF8FAF,0xAFBFAFBF,0xAFA6AFA6,0xAFA7AFA7),0x00000001,0x7B04BF73,10,'osCreateThread #10'),
  ((0x3C1A3C1A,0x275A275A,0x03400340,0x00000000,0x3C1A3C1A,0x275A275A,0xFF41FF41,0x401B401B),0x00000222,0x9EA512E4,1,'__osExceptionPreamble  #1'),
  ((0x3C1A3C1A,0x275A275A,0xFF41FF41,0x401B401B,0xAF5BAF5B,0x24012401,0x03610361,0x409B409B),0x00008022,0xFC437204,1,'__osException  #1'),
  ((0x3C0A3C0A,0x254A254A,0x01440144,0x8D498D49,0x03E003E0,0x11201120,0x00000000,0x8D2B8D2B),0x00008422,0xE07AFA48,0,'send_mesg'),
  ((0x3C013C01,0x01010101,0x00090009,0x240A240A,0x152A152A,0x00000000,0x8F5B8F5B,0x3C013C01),0x00004918,0x481AC224,0,'handle_CpU'),
  ((0x3C053C05,0x8CA58CA5,0x40084008,0x8CBB8CBB,0x35083508,0xACA8ACA8,0xFCB0FCB0,0xFCB1FCB1),0x00000012,0x73042C40,1,'__osEnqueueAndYield  #1'),
  ((0x8C988C98,0x8CAF8CAF,0x00800080,0x8F0E8F0E,0x01CF01CF,0x14201420,0x00000000,0x03000300),0x00000820,0x97A7BB74,1,'__osEnqueueThread  #1'),
  ((0x8C828C82,0x8C598C59,0x03E003E0,0xAC99AC99,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x0000579E,1,'__osPopThread  #1'),
  ((0x3C043C04,0x00000000,0x24842484,0x3C013C01,0xAC22AC22,0x24082408,0xA448A448,0x00400040),0x0000E434,0x08CBC6E4,1,'__osDispatchThread  #1'),
  ((0x00000000,0x00000000,0x00000000,0x00000000,0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFB2AFB2),0x00002010,0x12ECFAE7,1,'__osCleanupThread  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFB2AFB2,0xAFB1AFB1,0x00000000,0xAFB0AFB0,0x8FAE8FAE),0x00003201,0x0E471BAF,2,'osDestroyThread  #2'),
  ((0x3C023C02,0x03E003E0,0x8C428C42,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000004,0x00CCEA0F,1,'__osGetActiveQueue  #1'),
  ((0x14801480,0x00000000,0x3C043C04,0x8C848C84,0x03E003E0,0x8C828C82,0x00000000,0x00000000),0x00000009,0x00E1B01D,2,'osGetThreadId  #2'),
  ((0x14801480,0x00000000,0x3C043C04,0x8C848C84,0x03E003E0,0x8C828C82,0x00000000,0x00000000),0x00000009,0x00F1B01D,2,'osGetThreadPri #2'),
  ((0x27BD27BD,0xAFBFAFBF,0x00000000,0xAFB0AFB0,0x00000000,0x00400040,0xAFA2AFA2,0x3C0F3C0F),0x00003101,0x126BB64B,19,'osGetTime #19'),
  ((0x27BD27BD,0xAFBFAFBF,0x240E240E,0x3C013C01,0xAFB0AFB0,0xAFA0AFA0,0x00000000,0xAC2EAC2E),0x00004085,0x04AFB7CB,2,'osInitialize #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFB1AFB1,0x00000000,0xAFB0AFB0),0x00002001,0xD019FDBB,15,'osJamMesg #15'),
  ((0x3C013C01,0x03E003E0,0x00810081,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x00B6EA0F,29,'osPhysicalToVirtual #29'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFB1AFB1,0x00000000,0xAFB0AFB0),0x00004801,0x2359FDBB,14,'osRecvMesg #14'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFB0AFB0,0x8FAF8FAF,0x3C0E3C0E,0x8DCE8DCE),0x00004181,0xE0281BFB,1,'__osResetGlobalIntMask  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFB2AFB2,0xAFB1AFB1,0x00000000),0x00004001,0x361417EF,15,'osSendMesg #15'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0x00000000,0xAFB0AFB0,0x8FAE8FAE),0x00000401,0x1AFB59BB,16,'osSetEventMesg #16'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFB0AFB0,0x3C0E3C0E,0x8DCE8DCE,0x8FAF8FAF),0x00000841,0x00FF13FB,1,'__osSetGlobalIntMask  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0x00000000,0xAFB0AFB0,0x8FAF8FAF,0x8FAE8FAE),0x00004001,0x555B1ABB,1,'__osSetHWIntrRoutine  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0x00000000,0xAFB0AFB0,0x8FAE8FAE,0x00400040),0x00000901,0x4F2CCABB,18,'osSetThreadPri #18'),
  ((0xAFA4AFA4,0x8FAE8FAE,0xAFA5AFA5,0x3C013C01,0x8FAF8FAF,0xAC2EAC2E,0x3C013C01,0x03E003E0),0x00000120,0x000392F9,2,'osSetTime #2'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAE8FAE,0xAFBFAFBF,0xAFA6AFA6,0xAFA7AFA7,0xADC0ADC0,0x8FAF8FAF),0x00000001,0xB4E4AEBB,33,'osSetTimer #33'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFB1AFB1,0x00000000,0xAFB0AFB0,0x8FAE8FAE,0x24012401),0x00009C81,0xCACB063B,11,'osStartThread #11'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFB2AFB2,0xAFB1AFB1,0x00000000,0xAFB0AFB0,0x8FAE8FAE),0x00001A01,0x64071BAF,28,'osStopThread #28'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAE8FAE,0xAFBFAFBF,0xAFB0AFB0,0x8DCF8DCF,0x15E015E0,0x00000000),0x00004341,0x396BBF2F,34,'osStopTimer #34'),
  ((0x00800080,0x8CC78CC7,0x27BD27BD,0x10E010E0,0x00000000,0x14E514E5,0x00000000,0x8CAE8CAE),0x0000912C,0xDA4BB5D7,1,'__osDequeueThread  #1'),
  ((0x3C013C01,0x240E240E,0x240F240F,0xAC2FAC2F,0xAC2EAC2E,0x3C013C01,0x3C183C18,0x8F188F18),0x0000A59E,0xF15FD19C,1,'__osTimerServicesInit  #1'),
  ((0x3C0E3C0E,0x8DCE8DCE,0x27BD27BD,0xAFBFAFBF,0x8DCF8DCF,0x11EE11EE,0x00000000,0x3C183C18),0x00008526,0x782FB29C,1,'__osTimerInterrupt  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFA5AFA5,0x00000000,0xAFA2AFA2,0x3C013C01),0x00008501,0x2F6DB8F3,1,'__osSetTimerIntr  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0x00000000,0xAFA4AFA4,0x3C0E3C0E,0x8DCE8DCE,0xAFA2AFA2,0x8FB88FB8),0x00002021,0x3915AAC3,1,'__osInsertTimer  #1'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAE8FAE,0x3C013C01,0xAFBFAFBF,0x01C101C1,0x14201420,0x3C013C01),0x00001A41,0x0E2098EF,21,'osVirtualToPhysical #21'),
  ((0x40084008,0x31093109,0x24012401,0x00810081,0x012A012A,0x40894089,0x00000000,0x00000000),0x00008006,0xBAC8B3C8,1,'__osProbeTLB #1'),
  ((0x27BD27BD,0xAFBFAFBF,0x00000000,0xAFB0AFB0,0x3C0F3C0F,0x8DEF8DEF,0x240E240E,0x3C043C04),0x00000261,0x002F964B,2,'osYieldThread  #2'),
  ((0x3C023C02,0x03E003E0,0x8C428C42,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000004,0x00CCEA0F,1,'__osGetCurrFaultedThread  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFB1AFB1,0x00000000,0xAFB0AFB0,0x8FAE8FAE,0x00400040),0x00009901,0x922CC63B,1,'__osGetNextFaultedThread  #1'),
  ((0x3C0E3C0E,0x03E003E0,0x8DC28DC2,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x3C474E50,31,'osAiGetLength #31'),
  ((0x3C0E3C0E,0x03E003E0,0x8DC28DC2,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x3C4F4E50,2,'osAiGetStatus  #2'),
  ((0x3C0E3C0E,0x8DCE8DCE,0x44844484,0x27BD27BD,0x448E448E,0x46804680,0x04810481,0x46804680),0x0000800A,0xC813D50F,32,'osAiSetFrequency #32'),
  ((0x27BD27BD,0x3C0F3C0F,0x91EF91EF,0xAFA4AFA4,0x8FAE8FAE,0xAFBFAFBF,0xAFA5AFA5,0x11E011E0),0x0000A285,0x20D5C417,30,'osAiSetNextBuffer #30'),
  ((0x3C0E3C0E,0x8DC48DC4,0x3C013C01,0x27BD27BD,0x00810081,0x11E011E0,0x00000000,0x10001000),0x000009A8,0x3C8D5150,1,'__osAiDeviceBusy #1'),
  ((0x3C0E3C0E,0x03E003E0,0x8DC28DC2,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x3C4F4E10,2,'osDpGetStatus  #2'),
  ((0x3C0E3C0E,0x03E003E0,0xADC4ADC4,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x3C694E10,2,'osDpSetStatus  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA6AFA6,0xAFA7AFA7,0x00000000,0xAFB0AFB0,0x10401040),0x00000E81,0x6002E21B,2,'osDpSetNextBuffer  #2'),
  ((0x3C0E3C0E,0x8DC48DC4,0x27BD27BD,0x308F308F,0x11E011E0,0x00000000,0x10001000,0x24022402),0x000004DC,0x3C334480,1,'__osDpDeviceBusy  #1'),
  ((0x3C0E3C0E,0x8DCF8DCF,0x3C183C18,0x3C083C08,0xAC8FAC8F,0x8F198F19,0x24842484,0x3C0A3C0A),0x00004C40,0xE27700EC,2,'osDpGetCounters  #2'),
  ((0x3C0E3C0E,0x03E003E0,0x8DC28DC2,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x3C534E04,1,'__osSpGetStatus #1'),
  ((0x3C0E3C0E,0x03E003E0,0xADC4ADC4,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x3C754E04,1,'__osSpSetStatus #1'),
  ((0x3C0E3C0E,0x8DC58DC5,0x27BD27BD,0x30AF30AF,0x15E015E0,0x00000000,0x10001000,0x24022402),0x000010DC,0x785CE920,1,'__osSpSetPc #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFA5AFA5,0x10401040,0x00000000,0x10001000),0x000001A1,0x62EFF3C3,1,'__osSpRawReadIo  #1'),
  ((0x3C0E3C0E,0x8DC48DC4,0x27BD27BD,0x308F308F,0x11E011E0,0x00000000,0x10001000,0x24022402),0x000004DC,0x3C33449C,1,'__osSpDeviceBusy #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFA5AFA5,0x10401040,0x00000000,0x10001000),0x000001A1,0xC75BF3C3,1,'__osSpRawWriteIo  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0x00000000,0xAFA7AFA7,0x10401040),0x00000681,0x7F2A4C47,1,'__osSpRawStartDma #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0x8FA48FA4,0xAFA2AFA2,0x8FAE8FAE,0x8DCF8DCF),0x00001301,0xF94620D3,39,'osSpTaskLoad #39'),
  ((0x27BD27BD,0xAFBFAFBF,0x00000000,0xAFA4AFA4,0x10401040,0x00000000,0x00000000,0x00000000),0x00002911,0x14EFB143,22,'osSpTaskStartGo #22'),
  ((0x27BD27BD,0xAFBFAFBF,0x00000000,0x24042404,0x8FBF8FBF,0x27BD27BD,0x03E003E0,0x00000000),0x00000029,0x0000BE43,46,'osSpTaskYield #46'),
  ((0x27BD27BD,0xAFBFAFBF,0x00000000,0xAFA4AFA4,0xAFA2AFA2,0x8FAE8FAE,0x31CF31CF,0x11E011E0),0x0000C6C1,0x105EE503,47,'osSpTaskYielded #47'),
  ((0x27BD27BD,0xAFBFAFBF,0x3C043C04,0x24842484,0x00000000,0x24052405,0x3C0E3C0E,0x25CE25CE),0x00003AA9,0x0A2F9EC3,1,'__osViInit  #1'),
  ((0x3C0E3C0E,0x8DC28DC2,0x304F304F,0x03E003E0,0x01E001E0,0x00000000,0x00000000,0x00000000),0x00000004,0x3C03CEF0,2,'osViGetCurrentField #2'),
  ((0x27BD27BD,0xAFBFAFBF,0x00000000,0xAFB0AFB0,0x3C0E3C0E,0x8DCE8DCE,0x00400040,0x02000200),0x00008021,0xD92C2A4B,20,'osViGetCurrentFramebuffer #20'),
  ((0x27BD27BD,0xAFBFAFBF,0x00000000,0xAFB0AFB0,0x3C0E3C0E,0x8DCE8DCE,0x00400040,0x02000200),0x00008021,0xD92C2A4B,20,'osViGetNextFramebuffer #20'),
  ((0x3C0E3C0E,0x03E003E0,0x8DC28DC2,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x3C534E40,2,'osViGetCurrentLine #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFB1AFB1,0x00000000,0xAFB0AFB0,0x3C0E3C0E,0x8DCE8DCE,0x00400040),0x00000041,0xC6A8D0DB,2,'osViGetCurrentMode  #2'),
  ((0x3C0E3C0E,0x03E003E0,0x8DC28DC2,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x3C434E40,2,'osViGetStatus #2'),
  ((0x3C0E3C0E,0x8DCE8DCE,0x27BD27BD,0xAFBFAFBF,0x15C015C0,0xAFA4AFA4,0x00000000,0x00000000),0x0000AC16,0xF87FBB1C,55,'osCreateViManager #55'),
  ((0x3C023C02,0x03E003E0,0x8C428C42,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000004,0x00CCEA0F,1,'__osViGetCurrentContext  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0x00000000,0xAFB0AFB0,0x3C0F3C0F),0x00002101,0x506399BB,17,'osViSetEvent #17'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFB0AFB0,0x3C0F3C0F,0x8DEF8DEF,0x8FAE8FAE),0x00008A41,0xACCF63FB,2,'osViSetMode #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFB0AFB0,0x8FAE8FAE,0x00400040,0x31CF31CF),0x00002981,0x4C2FEFFB,2,'osViSetSpecialFeatures #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xE7ACE7AC,0xAFB1AFB1,0x00000000,0xAFB0AFB0,0x3C0E3C0E,0x8DCE8DCE),0x00009081,0xC66E162B,2,'osViSetXScale  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xE7ACE7AC,0x00000000,0xAFB0AFB0,0x3C0E3C0E,0x8DCE8DCE,0xC7A4C7A4),0x00004841,0xED0B93EB,2,'osViSetYScale  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0x00000000,0xAFA4AFA4,0x3C0F3C0F,0x8DEF8DEF,0x8FAE8FAE,0xAFA2AFA2),0x00001421,0x4A93A603,23,'osViSwapBuffer #23'),
  ((0x27BD27BD,0xAFB1AFB1,0xAFBFAFBF,0xAFB2AFB2,0xAFB0AFB0,0xAFA0AFA0,0x3C113C11,0x3C0E3C0E),0x00000901,0xFB6943CF,1,'__osViSwapContext  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFB0AFB0,0x93AE93AE,0x00400040,0x11C011C0),0x00003481,0x2C1E6BFB,2,'osViBlack #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0x00000000,0xAFB0AFB0,0x93AE93AE,0x00400040),0x00003101,0xF96DDABB,2,'osViFade  #2'),
  ((0x3C0E3C0E,0x03E003E0,0x8DC28DC2,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x3C5B4E80,1,'__osSiGetStatus  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFA5AFA5,0x10401040,0x00000000,0x10001000),0x000001A1,0x62EFF3C3,1,'__osSiRawReadIo #1'),
  ((0x3C0E3C0E,0x8DC48DC4,0x27BD27BD,0x308F308F,0x11E011E0,0x00000000,0x10001000,0x24022402),0x000004DC,0x3C334410,1,'__osSiDeviceBusy #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFA5AFA5,0x10401040,0x00000000,0x10001000),0x000001A1,0xC75BF3C3,1,'__osSiRawWriteIo #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFA5AFA5,0x10401040,0x00000000,0x10001000),0x00008DA1,0xCFAFF3C3,1,'__osSiRawStartDma #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFA0AFA0,0x3C0E3C0E,0x91CE91CE,0x11C011C0),0x000050C1,0x344E73D3,42,'osContStartQuery #42'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x8FA58FA5,0x00000000,0x27A427A4,0x8FBF8FBF,0x27BD27BD),0x000000A1,0x000E46D3,43,'osContGetQuery #43'),
  ((0x27BD27BD,0xAFBFAFBF,0x240E240E,0x3C013C01,0x3C043C04,0x3C053C05,0xAC2EAC2E,0x24A524A5),0x000015C5,0x434E72C3,1,'__osSiCreateAccessQueue #1'),
  ((0x3C0E3C0E,0x8DCE8DCE,0x27BD27BD,0xAFBFAFBF,0x15C015C0,0x00000000,0x00000000,0x00000000),0x00005616,0x274FB39C,1,'__osSiGetAccess #1'),
  ((0x27BD27BD,0xAFBFAFBF,0x3C043C04,0x24842484,0x00000000,0x00000000,0x00000000,0x8FBF8FBF),0x00000109,0x000D6BC3,1,'__osSiRelAccess #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFA0AFA0,0x3C0E3C0E,0x91CE91CE,0x24012401),0x0000A1C1,0x846C33D3,26,'osContStartReadData #26'),
  ((0x3C0F3C0F,0x91EF91EF,0x3C0E3C0E,0x27BD27BD,0x25CE25CE,0xAFAEAFAE,0x19E019E0,0xAFA0AFA0),0x0000025A,0x86C18908,27,'osContGetReadData #27'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFA5AFA5,0x3C0E3C0E,0x91CE91CE,0x24012401),0x0000A1C1,0x846C32D3,2,'osContReset  #2'),
  ((0x27BD27BD,0xAFA0AFA0,0x8FAE8FAE,0x8FB88FB8,0x3C013C01,0x000E000E,0x002F002F,0xAC20AC20),0x0000A781,0xFCECCE97,1,'__osPackResetData  #1'),
  ((0x27BD27BD,0x3C0E3C0E,0x8DCE8DCE,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0x11C011C0),0x00004A85,0x04BA4E47,25,'osContInit #25'),
  ((0x3C0F3C0F,0x91EF91EF,0x27BD27BD,0x3C0E3C0E,0x25CE25CE,0xA3A0A3A0,0xAFAEAFAE,0x19E019E0),0x00000496,0x6D7C65D8,1,'__osContGetInitData  #1'),
  ((0x27BD27BD,0x30843084,0xAFA0AFA0,0x8FAE8FAE,0x8FB88FB8,0x3C013C01,0x000E000E,0x002F002F),0x00004F03,0x19C74027,1,'__osPackRequestData  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0x00000000,0xAFA6AFA6,0x8FA48FA4,0x00000000),0x00002801,0xCF9F02EB,2,'osPfsReFormat  #2'),
  ((0x27BD27BD,0x8FB88FB8,0x3C0E3C0E,0x25CE25CE,0x240F240F,0x24012401,0xAFBFAFBF,0xAFA4AFA4),0x00004039,0x28E40ACB,1,'__osContRamWrite  #1'),
  ((0x27BD27BD,0x30843084,0xA3A0A3A0,0xAFA0AFA0,0x93AE93AE,0x31CF31CF,0x11E011E0,0x00000000),0x0000A363,0xB1DAA457,1,'__osContAddressCrc  #1'),
  ((0x27BD27BD,0xA3A0A3A0,0xAFA0AFA0,0x240E240E,0xAFAEAFAE,0x93AF93AF,0x31F831F8,0x13001300),0x000086C9,0x915A314B,1,'__osContDataCrc  #1'),
  ((0x27BD27BD,0xAFA0AFA0,0xAFA4AFA4,0x18A018A0,0xAFA0AFA0,0x8FAF8FAF,0x8FAE8FAE,0x8FAB8FAB),0x00000609,0x27AAAE2F,1,'__osSumcalc  #1'),
  ((0x27BD27BD,0xA7A0A7A0,0xA4C0A4C0,0x94CE94CE,0xA4AEA4AE,0xAFA0AFA0,0x8FAF8FAF,0x008F008F),0x00000001,0x458111C3,1,'__osIdCheckSum  #1'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAE8FAE,0xAFBFAFBF,0xAFA5AFA5,0xAFA6AFA6,0xAFA0AFA0,0xA3A0A3A0),0x00000201,0x84084413,1,'__osRepairPackId  #1'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAE8FAE,0xAFBFAFBF,0xAFA5AFA5,0xAFA0AFA0,0x91CF91CF,0x11E011E0),0x00004081,0x38EAD507,1,'__osCheckPackId  #1'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAE8FAE,0xAFBFAFBF,0x91CF91CF,0x11E011E0,0x00000000,0xA1C0A1C0),0x00005021,0x0985F787,1,'__osGetId  #1'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAE8FAE,0xAFBFAFBF,0x91CF91CF,0x11E011E0,0x00000000,0xA1C0A1C0),0x00005021,0x09D5F787,1,'__osCheckId  #1'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAE8FAE,0xAFBFAFBF,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0x91CF91CF),0x00008101,0x955F1907,1,'__osPfsRWInode  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA0AFA0,0xAFA0AFA0,0x8FAE8FAE,0x8FB88FB8,0x91CF91CF),0x00003801,0x5138124B,1,'__osPfsSelectBank  #1'),
  ((0x27BD27BD,0x3C0E3C0E,0xAFBFAFBF,0x25CE25CE,0x240F240F,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6),0x00004019,0x18741AD7,1,'__osContRamRead  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA0AFA0,0x00000000,0x8FA48FA4,0xAFA2AFA2,0x8FAE8FAE),0x00008301,0x4D40AA6B,2,'osPfsChecker  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA0AFA0,0x8FAE8FAE,0x8FAF8FAF,0x01CF01CF),0x00009C01,0x014D1113,0,'corrupted_init'),
  ((0x27BD27BD,0xAFA5AFA5,0x93B893B8,0x93AE93AE,0xAFA4AFA4,0x8FAA8FAA,0xAFBFAFBF,0xAFA6AFA6),0x00009001,0xBB51277F,0,'corrupted'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0x00000000,0xAFA0AFA0,0x8FA48FA4),0x0000A001,0x5665DA13,2,'osPfsInit  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA0AFA0,0x00000000,0x00000000,0x3C053C05),0x0000A501,0x096DBBE3,1,'__osPfsGetStatus  #1'),
  ((0x27BD27BD,0xAFA5AFA5,0x97AE97AE,0xAFBFAFBF,0xAFA4AFA4,0xAFA6AFA6,0xAFA7AFA7,0xAFA0AFA0),0x0000A401,0x59FF4E7B,2,'osPfsAllocateFile  #2'),
  ((0x27BD27BD,0x93AE93AE,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0x19C019C0),0x00000681,0xC690E4B3,1,'__osPfsDeclearPage  #1'),
  ((0x27BD27BD,0xAFA5AFA5,0x97AE97AE,0xAFBFAFBF,0xAFA4AFA4,0xAFA6AFA6,0xAFA7AFA7,0x11C011C0),0x00003481,0x2E454E7B,2,'osPfsDeleteFile  #2'),
  ((0x27BD27BD,0xAFA6AFA6,0x93B893B8,0xAFA5AFA5,0x8FAF8FAF,0x00180018,0xAFBFAFBF,0xAFA4AFA4),0x00009001,0x82C6EE97,1,'__osPfsReleasePages  #1'),
  ((0x27BD27BD,0xAFA4AFA4,0xAFA7AFA7,0x93AE93AE,0x8FAF8FAF,0xAFBFAFBF,0xAFA5AFA5,0xAFA6AFA6),0x00004001,0x38E7B6E7,1,'__osBlockSum  #1'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAF8FAF,0xAFA5AFA5,0xAFBFAFBF,0xAFA6AFA6,0xAFA7AFA7,0x8FAE8FAE),0x0000C401,0x4A78E67F,2,'osPfsReadWriteFile  #2'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAF8FAF,0xAFA5AFA5,0xAFBFAFBF,0xAFA6AFA6,0x8FAE8FAE,0x8DF88DF8),0x00006201,0x4F0300D7,2,'osPfsFileState  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xAFA0AFA0,0x00000000),0x00003601,0x1E461E43,2,'osPfsFindFile  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0x00000000,0x8FA48FA4,0x24012401,0x14411441),0x000016C1,0xE8DA9EBB,2,'osPfsSetLabel  #2'),
  ((0x27BD27BD,0xAFA5AFA5,0x8FAE8FAE,0xAFBFAFBF,0xAFA4AFA4,0x15C015C0,0xAFA6AFA6,0x10001000),0x0000D9A1,0x4BDFCAAB,2,'osPfsGetLabel  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0x240E240E,0xAFA4AFA4,0xAFA5AFA5,0xAFA0AFA0,0xA3A0A3A0,0x00000000),0x00005005,0xB44C11C3,2,'osPfsIsPlug  #2'),
  ((0x27BD27BD,0x30843084,0x3C013C01,0xA024A024,0xAFA0AFA0,0x8FAE8FAE,0x8FB88FB8,0x3C013C01),0x00003C0B,0x33D1AD07,1,'__osPfsRequestData  #1'),
  ((0x3C0F3C0F,0x91EF91EF,0x27BD27BD,0x3C0E3C0E,0x25CE25CE,0xA3A0A3A0,0xAFAEAFAE,0x19E019E0),0x00000496,0x6D7C65D8,1,'__osPfsGetInitData  #1'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAE8FAE,0xAFBFAFBF,0xAFA5AFA5,0xAFA0AFA0,0xAFA0AFA0,0x8DCF8DCF),0x00009B01,0x860246BB,2,'osPfsFreeBlocks  #2'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAE8FAE,0xAFBFAFBF,0xAFA5AFA5,0xAFA6AFA6,0xAFA0AFA0,0x8DCF8DCF),0x00009B01,0x96025FAF,2,'osPfsNumFiles  #2'),
  ((0x27BD27BD,0xAFA5AFA5,0x97AE97AE,0xAFBFAFBF,0xAFA4AFA4,0xAFA6AFA6,0xAFA7AFA7,0xAFA0AFA0),0x00004001,0xE5354E7B,2,'osPfsReSizeFile  #2'),
  ((0x27BD27BD,0xAFA5AFA5,0x93AF93AF,0x3C0E3C0E,0x25CE25CE,0x29E129E1,0xAFBFAFBF,0xAFA4AFA4),0x00006831,0xCFF4A5D7,58,'osEepromRead #58'),
  ((0x27BD27BD,0xAFA5AFA5,0x93AF93AF,0x3C0E3C0E,0x25CE25CE,0x29E129E1,0xAFBFAFBF,0xAFA4AFA4),0x00003431,0x0E64A5D7,59,'osEepromWrite #59'),
  ((0x27BD27BD,0x3C0E3C0E,0x25CE25CE,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA0AFA0,0xAFAEAFAE),0x0000C005,0x0A462BA7,1,'__osEepStatus #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFA0AFA0,0x8FA48FA4,0x00000000,0x27A527A5),0x00006481,0x396AB7D3,57,'osEepromProbe #57'),
  ((0x27BD27BD,0xAFA5AFA5,0x93AE93AE,0xAFBFAFBF,0xAFA4AFA4,0x29C129C1,0xAFA6AFA6,0xAFA7AFA7),0x00002D21,0x971CBD47,61,'osEepromLongWrite #61'),
  ((0x27BD27BD,0xAFA5AFA5,0x93AE93AE,0xAFBFAFBF,0xAFA4AFA4,0x29C129C1,0xAFA6AFA6,0xAFA7AFA7),0x00002D21,0x971CBD47,60,'osEepromLongRead #60'),
  ((0x3C023C02,0x03E003E0,0x8C428C42,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x00CBEA0F,2,'osPiGetDeviceType  #2'),
  ((0x3C0E3C0E,0x03E003E0,0x8DC28DC2,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x3C534E60,2,'osPiGetStatus  #2'),
  ((0x3C0E3C0E,0x8DC68DC6,0x27BD27BD,0x30CF30CF,0x11E011E0,0x00000000,0x3C183C18,0x8F068F06),0x0000031C,0x106FF910,2,'osPiRawReadIo  #2'),
  ((0x3C0E3C0E,0x8DC68DC6,0x27BD27BD,0x30CF30CF,0x11E011E0,0x00000000,0x3C183C18,0x8F068F06),0x0000431C,0x106FF910,2,'osPiRawWriteIo  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xAFB1AFB1,0xAFB0AFB0),0x00008C01,0x83360A7B,2,'osPiRawStartDma #2'),
  ((0x27BD27BD,0x3C0E3C0E,0x8DCE8DCE,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0x15C015C0),0x00008085,0xFA781B07,2,'osCreatePiManager #2'),
  ((0x3C0E3C0E,0x8DC78DC7,0x27BD27BD,0x30EF30EF,0x11E011E0,0x00000000,0x3C183C18,0x8F078F07),0x0000031C,0x6CEDB894,2,'osEPiRawReadIo #2'),
  ((0x3C0E3C0E,0x8DC78DC7,0x27BD27BD,0x30EF30EF,0x11E011E0,0x00000000,0x3C183C18,0x8F078F07),0x0000231C,0x6CEDB894,2,'osEPiRawWriteIo  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xAFB1AFB1,0xAFB0AFB0),0x00008C01,0x83360A7B,2,'osEPiRawStartDma  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0x00000000,0xAFB0AFB0,0x8FA48FA4),0x00000001,0x0E6D59BB,2,'osEPiWriteIo  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0x00000000,0xAFB0AFB0,0x8FA48FA4),0x00000001,0x0E6D59BB,2,'osEPiReadIo  #2'),
  ((0x27BD27BD,0x3C0E3C0E,0x8DCE8DCE,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFB1AFB1),0x00000D05,0xD9187407,37,'osEPiStartDma #37'),
  ((0x3C0E3C0E,0x8DCE8DCE,0x15C015C0,0x00000000,0x03E003E0,0x00000000,0x00000000,0x00000000),0x00000006,0x00313A6F,2,'osPiGetCmdQueue  #2'),
  ((0x3C013C01,0x27BD27BD,0xA020A020,0xAFBFAFBF,0x3C013C01,0x3C0E3C0E,0xAFA0AFA0,0xAC2EAC2E),0x0000C186,0x584E9288,2,'osCartRomInit  #2'),
  ((0x240E240E,0x3C013C01,0xA02EA02E,0x3C013C01,0x3C0F3C0F,0xAC2FAC2F,0x3C013C01,0x24182418),0x0000EDA5,0x385030D6,2,'osLeoDiskInit  #2'),
  ((0x3C0E3C0E,0x8DCE8DCE,0x27BD27BD,0xAFBFAFBF,0x15C015C0,0x00000000,0x10001000,0x00000000),0x00000A56,0x6357077C,1,'__osLeoInterrupt  #1'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAE8FAE,0xAFBFAFBF,0xAFA0AFA0,0xAFA0AFA0,0xAFA0AFA0,0xAFAEAFAE),0x00008601,0x1D4D8107,1,'__osDevMgrMain #1'),
  ((0x27BD27BD,0xAFBFAFBF,0x240E240E,0x3C013C01,0x3C043C04,0x3C053C05,0xAC2EAC2E,0x24A524A5),0x000015C5,0x434E72C3,1,'__osPiCreateAccessQueue  #1'),
  ((0x3C0E3C0E,0x8DCE8DCE,0x27BD27BD,0xAFBFAFBF,0x15C015C0,0x00000000,0x00000000,0x00000000),0x00005616,0x274FB39C,1,'__osPiGetAccess  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0x3C043C04,0x24842484,0x00000000,0x00000000,0x00000000,0x8FBF8FBF),0x00000109,0x000D6BC3,1,'__osPiRelAccess  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0x00000000,0xAFB0AFB0,0x8FA48FA4,0x00000000),0x00008001,0xDA1D0ABB,2,'osPiWriteIo  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0x00000000,0xAFB0AFB0,0x8FA48FA4,0x00000000),0x00008001,0xDA1D0ABB,2,'osPiReadIo  #2'),
  ((0x27BD27BD,0x3C0E3C0E,0x8DCE8DCE,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7),0x00005A05,0x1E15B407,12,'osPiStartDma #12'),
  ((0x28C128C1,0x14201420,0x00850085,0x30423042,0x14401440,0x00040004,0x33183318,0x13001300),0x0000C0DB,0xBB8C0CCE,0,'bcmp'),
  ((0x10C010C0,0x00A000A0,0x10851085,0x00A400A4,0x54205420,0x28C128C1,0x00860086,0x00A200A2),0x0000BE25,0xD1D5189A,0,'bcopy'),
  ((0x28A128A1,0x14201420,0x00040004,0x30633063,0x10601060,0x00A300A3,0xA880A880,0x00830083),0x0000251B,0x5980BB1D,0,'bzero'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DDDB1,0,'__ull_rshift'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DDDB1,0,'A__ull_rshift'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DDDB1,0,'A__ull_rshift'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DDDB1,0,'A__ull_rshift'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x180E8DB1,5,'__ull_rem #5'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x180E8DB1,5,'A__ull_rem #5'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x180E8DB1,5,'A__ull_rem #5'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x180E8DB1,5,'A__ull_rem #5'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x182E8DB1,3,'__ull_div #3'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x182E8DB1,3,'A__ull_div #3'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x182E8DB1,3,'A__ull_div #3'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x182E8DB1,3,'A__ull_div #3'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DFDB1,0,'__ll_lshift'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DFDB1,0,'A__ll_lshift'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DFDB1,0,'A__ll_lshift'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DFDB1,0,'A__ll_lshift'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x180E8DB1,5,'__ll_rem #5'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x180E8DB1,5,'A__ll_rem #5'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x180E8DB1,5,'A__ll_rem #5'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x180E8DB1,5,'A__ll_rem #5'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x00000000),0x00009100,0xF28E9DB1,6,'__ll_div #6'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x00000000),0x00009100,0xF28E9DB1,6,'A__ll_div #6'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x00000000),0x00009100,0xF28E9DB1,6,'A__ll_div #6'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x00000000),0x00009100,0xF28E9DB1,6,'A__ll_div #6'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x00000000),0x00000000,0x00432DB1,4,'__ll_mul #4'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x00000000),0x00000000,0x00432DB1,4,'A__ll_mul #4'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x00000000),0x00000000,0x00432DB1,4,'A__ll_mul #4'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x00000000),0x00000000,0x00432DB1,4,'A__ll_mul #4'),
  ((0x87AF87AF,0xAFA6AFA6,0xAFA7AFA7,0xDFAEDFAE,0x01E001E0,0x03000300,0x01D901D9,0x17201720),0x00000080,0xD4AEE0B3,0,'__ull_divremi'),
  ((0x87AF87AF,0xAFA6AFA6,0xAFA7AFA7,0xDFAEDFAE,0x01E001E0,0x03000300,0x01D901D9,0x17201720),0x00000080,0xD4AEE0B3,0,'A__ull_divremi'),
  ((0x87AF87AF,0xAFA6AFA6,0xAFA7AFA7,0xDFAEDFAE,0x01E001E0,0x03000300,0x01D901D9,0x17201720),0x00000080,0xD4AEE0B3,0,'A__ull_divremi'),
  ((0x87AF87AF,0xAFA6AFA6,0xAFA7AFA7,0xDFAEDFAE,0x01E001E0,0x03000300,0x01D901D9,0x17201720),0x00000080,0xD4AEE0B3,0,'A__ull_divremi'),
  ((0x27BD27BD,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF),0x00002201,0xBC4E2F5B,0,'__ll_mod'),
  ((0x27BD27BD,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF),0x00002201,0xBC4E2F5B,0,'A__ll_mod'),
  ((0x27BD27BD,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF),0x00002201,0xBC4E2F5B,0,'A__ll_mod'),
  ((0x27BD27BD,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF),0x00002201,0xBC4E2F5B,0,'A__ll_mod'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DCDB1,0,'__ll_rshift'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DCDB1,0,'A__ll_rshift'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DCDB1,0,'A__ll_rshift'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DCDB1,0,'A__ll_rshift'),
  ((0x27BD27BD,0xAFA4AFA4,0xAFBFAFBF,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0x3C043C04,0x24842484),0x00000181,0xCA649E3B,0,'sprintf'),
  ((0x00800080,0x10C010C0,0x00A000A0,0x906E906E,0x24C624C6,0x24422442,0x24632463,0x14C014C0),0x000000F2,0x001E42BD,0,'memcpy'),
  ((0x908E908E,0x00800080,0x11C011C0,0x00000000,0x906F906F,0x24632463,0x55E055E0,0x906F906F),0x00000024,0x0006FCD8,0,'strlen'),
  ((0x90839083,0x30AE30AE,0x30A230A2,0x51C351C3,0x00800080,0x54605460,0x90839083,0x03E003E0),0x00000006,0x00018CBE,0,'strchr'),
  ((0x27BD27BD,0xAFB7AFB7,0xAFB6AFB6,0xAFB5AFB5,0xAFBEAFBE,0xAFB4AFB4,0xAFB3AFB3,0xAFA7AFA7),0x00000001,0x486FA0F3,0,'_Printf'),
  ((0x27BD27BD,0xAFB1AFB1,0x30A230A2,0x24032403,0x00800080,0xAFBFAFBF,0xAFB3AFB3,0xAFB2AFB2),0x0000B20D,0x3A6991FF,0,'_Litob'),
  ((0x27BD27BD,0xAFA4AFA4,0xAFBFAFBF,0xAFA6AFA6,0xAFA7AFA7,0x00C000C0,0x00E000E0,0x8FA78FA7),0x00000001,0xD14D8F7F,0,'lldiv'),
  ((0x00A600A6,0x00000000,0x27BD27BD,0x14C014C0,0x00000000,0x00070007,0x24012401,0x14C114C1),0x000042CC,0x500B111E,0,'ldiv'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFB5AFB5,0xAFB4AFB4,0xAFB3AFB3,0xAFB2AFB2,0xAFB1AFB1,0xAFB0AFB0),0x00009001,0xFEF33863,0,'_Ldtob'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x00000000),0x00009100,0xF28E964B,6,'__ll_div #6'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x00000000),0x00009100,0xF28E964B,6,'A__ll_div #6'),
]
ULTRAHLE_OSPATCH: List[str] = [
  'osSpTaskLoad #39',
  'osSpTaskStartGo #22',
  'osSpTaskYield #46',
  'osSpTaskYielded #47',
  '__osSpSetStatus #1',
  '__osSpSetPc #1',
  '__osSpRawStartDma #1',
  '__osSpDeviceBusy #1',
  '__osSpGetStatus #1',
  '__ull_rshift #9',
  '__ull_rem #5',
  '__ull_div #3',
  '__ll_lshift #9',
  '__ll_rem #5',
  '__ll_div #6',
  '__ll_mul #4',
  '__ull_divremi #9',
  '__ll_mod #9',
  '__ll_rshift #9',
  'osSetTime #2',
  'osMapTLB #24',
  'osMapTLBRdb #2',
  'osCreateMesgQueue #13',
  'osSetEventMesg #16',
  'osViSetEvent #17',
  'osCreateThread #10',
  'osRecvMesg #14',
  'osViGetCurrentField #2',
  'osViGetCurrentLine #2',
  'osViGetStatus #2',
  'osSendMesg #15',
  'osStartThread #11',
  'osStopThread #28',
  'osWriteBackDCacheAll #1',
  'osCreateViManager #55',
  'osViSetMode #2',
  'osViBlack #2',
  'osViSetSpecialFeatures #2',
  'osCreatePiManager #2',
  'osSetThreadPri #18',
  'osInitialize #2',
  'osViSwapBuffer #23',
  'osViGetCurrentFramebuffer #20',
  'osViGetNextFramebuffer #20',
  'osContStartReadData #26',
  'osContGetReadData #27',
  'osContStartQuery #42',
  'osContGetQuery #43',
  'osContInit #25',
  'osEepromProbe #57',
  'osInvalDCache #1',
  'osInvalICache #38',
  'osPiStartDma #12',
  'osEPiStartDma #37',
  'osInvalCache #1',
  'osEepromLongRead #60',
  'osEepromLongWrite #61',
  'osGetTime #19',
  'osAiSetFrequency #32',
  'osWriteBackDCache #2',
  'osAiGetLength #31',
  'osAiSetNextBuffer #30',
  'osVirtualToPhysical #21',
  'osPhysicalToVirtual #29',
  'osGetThreadPri #2',
  'osGetCount #48',
  'osPiRawStartDma #2',
  'osMapTLBRdb #2',
  'osEPiRawReadIo #2',
  'osSetTimer #33',
  'osStopTimer #34',
  'osEepromWrite #59',
  'osJamMesg #15',
  'osEepromRead #58',
  'osSetIntMask #2',
  '__osDisableInt #1',
  '__osRestoreInt #1',
  '__ososViDevMgrMain #1',
  '__ososContGetInitData #1',
  '__ososPackRequestData #1',
  '__ososTimerServicesInit #1',
  '__ososTimerInterrupt #1',
  '__ososSetTimerIntr #1',
  '__ososInsertTimer #1',
  '__ososViInit #1',
  '__ososExceptionPreamble #1',
  '__ososEnqueueAndYield #1',
  '__ososEnqueueThread #1',
  '__ososPopThread #1',
  '__ososDispatchThread #1',
  '__ososCleanupThread #1',
  '__ososPiCreateAccessQueue #1',
  '__ososPiGetAccess #1',
  '__ososPiRelAccess #1',
  '__osDevMgrMain #1',
  '__osGetSR #1',
  '__osSetFpcCsr #1',
  '__osSiRawReadIo #1',
  '__osSiRawWriteIo #1',
  '__osSiCreateAccessQueue #1',
  '__osSiGetAccess #1',
  '__osSiRelAccess #1',
  '__osSiRawStartDma #1',
  '__osEepStatus #1',
  '__osAiDeviceBusy #1',
  '__osSetCompare #1',
  '__osProbeTLB #1',
  '__osSyncPutChars #1',
  '__osSiDeviceBusy #1',
  '__ososAtomicDec #1',
  '__osViDevMgr #1',
  '__osPiDevMgr #1',
  '__osRunQueue #1',
  '__osActiveQueue #1',
  '__osRunningThread #1',
  '__osViNext #1',
  '__osPiAccessQueueEnabled #1',
  '__osRcpImTable #1',
  '__osEventStateTab #1',
  '__osMyViThread #1',
  '__osMyViStack #1',
  '__osMyViQueue #1',
  '__osMyViMesg #1',
  '__osCurrentTime #1',
  '__osCurrentTime_2 #1',
  '__osBaseCounter #1',
  '__os* #1',
  'os* #2',
]
ULTRAHLE_DISABLE_PATCHES: Tuple[str, ...] = (
  'osPiGetDeviceType',
  'osPiGetStatus',
  'osPiRawReadIo',
  'osPiRawWriteIo',
  'osPiRawStartDma',
  'osPiGetCmdQueue',
  '__osPiDevMgr',
  '__osPiTable',
  '__osPiAccessQueueEnabled',
  '__osPiCreateAccessQueue',
  '__osPiGetAccess',
  '__osPiRelAccess',
  'osPiWriteIo',
  'osPiReadIo',
  '__osPfsPifRam',
  'osPfsReFormat',
  '__osPfsRWInode',
  '__osPfsSelectBank',
  'osPfsInit',
  '__osPfsGetStatus',
  'osPfsAllocateFile',
  '__osPfsDeclearPage',
  'osPfsDeleteFile',
  '__osPfsReleasePages',
  'osPfsReadWriteFile',
  'osPfsFileState',
  'osPfsFindFile',
  'osPfsSetLabel',
  'osPfsGetLabel',
  'osPfsIsPlug',
  '__osPfsRequestData',
  '__osPfsGetInitData',
  'osPfsFreeBlocks',
  'osPfsNumFiles',
  'osPfsReSizeFile',
  # Cont/SI: keep HLE patches enabled — __osException is patched to skip, so
  # hardware SI completion never runs; ContStartReadData must fire OS_EVENT_SI.
  'osContReset',
  '__osContRamWrite',
  '__osContAddressCrc',
  '__osContDataCrc',
  '__osContRamRead',
  '__osContPifRam',
  '__osContLastCmd',
  '__osContinitialized',
  '__osSiGetStatus',
  '__osSiRawReadIo',
  '__osSiDeviceBusy',
  '__osSiRawWriteIo',
  '__osSiRawStartDma',
  '__osSiCreateAccessQueue',
  '__osSiGetAccess',
  '__osSiRelAccess',
  '__osSiAccessQueue',
  '__osSiAccessQueueEnabled',
  '__osGetCause',
  '__osGetCompare',
  '__osGetConfig',
  '__osGetFpcCsr',
  '__osGetSR',
  '__osGetTLBASID',
  '__osGetTLBHi',
  '__osGetTLBLo0',
  '__osGetTLBLo1',
  '__osGetTLBPageMask',
  '__osSetCause',
  '__osSetCompare',
  '__osSetConfig',
  '__osSetCount',
  '__osSetFpcCsr',
  '__osSetSR',
)
ULTRAHLE_INI_PROFILES: Dict[str, Dict[str, Any]] = {
  'SUPER MARIO': {
      'alttitle': 'Super Mario 64', 'osrange': (0x80300000, 0x80380000),
      'ismario': 1, 'optimize': 3,
  },
  'THE LEGEND ': {
      'alttitle': 'Zelda: Ocarina of Time', 'osrange': (0x80001000, 0x80008000),
      'iszelda': 1, 'optimize': 3,
      'patches': [
          (0, 0x80005BA0, 'patch', 2),
          (0, 0x80003500, 'patch', 2),
          (0, 0x800012A0, 'patch', 2),
          (0, 0x80001600, 'patch', 2),
          (0, 0x80005130, 'patch', 2),
          (-1, 0x8011B9D9, 'byte', 1),  # English
      ],
  },
  'ZELDA': {'alttitle': 'Zelda', 'osrange': (0x80001000, 0x80010000), 'iszelda': 1, 'optimize': 3},
  'Wave Race': {'osrange': (0x800C0000, 0x800F0000)},
  'WAVE RACE': {'osrange': (0x800C0000, 0x800F0000)},
  'Banjo-Kazooie': {
      'bootloader': 1, 'osrange': (0x80000000, 0x80010000),
      'patches': [
          (0, 0x8000052C, 'patch', 49),
          (0, 0x80000530, 'word', 0x0320F809),
          (0, 0x80000534, 'word', 0x8FA40020),
      ],
  },
  'BANJO': {
      'bootloader': 1, 'osrange': (0x80000000, 0x80010000),
      'patches': [
          (0, 0x8000052C, 'patch', 49),
          (0, 0x80000530, 'word', 0x0320F809),
          (0, 0x80000534, 'word', 0x8FA40020),
      ],
  },
  'GoldenEye': {'osrange': (0x80008000, 0x80024000)},
  'GOLDENEYE': {'osrange': (0x80008000, 0x80024000)},
  'MARIOKART': {'osrange': (0x80000000, 0x80100000)},
  'MARIO KART': {'osrange': (0x80000000, 0x80100000)},
  'STAR FOX': {'osrange': (0x80000000, 0x80100000)},
  'STARFOX': {'osrange': (0x80000000, 0x80100000)},
  'F-ZERO': {'bootloader': 1, 'osrange': (0x80000000, 0x80100000)},
  'DONKEY KONG': {'osrange': (0x80000000, 0x80100000)},
  'PAPER MARIO': {'osrange': (0x80000000, 0x80100000)},
  'SMASH BROS': {'osrange': (0x80000000, 0x80100000)},
  'Doom': {'osrange': (0x80000000, 0x80100000)},
  'DOOM': {'osrange': (0x80000000, 0x80100000)},
  'Quake': {'osrange': (0x80000000, 0x80100000)},
  'QUAKE': {'osrange': (0x80000000, 0x80100000)},
}


# ── UltraHLE SYM.C / PATCH install (signature scan + OP_PATCH rewrite) ──
ADDRMASK_UH = 0x3FFFFFFF
ULTRAHLE_CODESIZE = 0x100000  # boot.c cart.codesize default


def _uh_op_op(word: int) -> int:
    return (word >> 26) & 0x3F


def _uh_op_imm(word: int) -> int:
    return word & 0xFFFF


def ultrahle_match_ini(title: str) -> Dict[str, Any]:
    t = (title or "").upper()
    for key, prof in ULTRAHLE_INI_PROFILES.items():
        if t.startswith(key.upper()) or key.upper() in t:
            return dict(prof)
    # title field is often "SUPER MARIO 64      "
    for key, prof in ULTRAHLE_INI_PROFILES.items():
        if key.upper().rstrip() in t:
            return dict(prof)
    return {}


class UltraHleSym:
    """Port of UltraHLE sym.c — find libultra by CRC and rewrite to OP_PATCH."""

    __slots__ = (
        "core", "syms", "found", "patches_applied", "first_patch", "last_patch",
        "osrange", "ismario", "iszelda", "bootloader", "ini_patches",
        "codebase", "codesize", "last_report", "yield_addrs",
    )

    def __init__(self, core: "ACsN64Core"):
        self.core = core
        self.reset()

    def reset(self):
        self.syms: List[Dict[str, Any]] = [{"addr": 0, "text": "(null)", "patch": 0, "original": 0}]
        self.found: Dict[int, Dict[str, Any]] = {}
        self.patches_applied = 0
        self.first_patch = 0
        self.last_patch = 0
        self.osrange = (0, 0)
        self.ismario = 0
        self.iszelda = 0
        self.bootloader = 0
        self.ini_patches: List[Tuple] = []
        self.codebase = 0x80000400
        self.codesize = ULTRAHLE_CODESIZE
        self.last_report = ""
        self.yield_addrs: set = set()

    def _rd32(self, addr: int) -> int:
        return self.core.bus.read_u32(u32(addr))

    def _wr32(self, addr: int, val: int):
        self.core.bus.write_u32(u32(addr), u32(val))

    def _disabled(self, name: str) -> bool:
        base = name.split("#", 1)[0].strip()
        for d in ULTRAHLE_DISABLE_PATCHES:
            if base == d or base.startswith(d):
                return True
        return False

    def add_symbol(self, addr: int, text: str, patch: int) -> int:
        addr &= ADDRMASK_UH
        if self._disabled(text):
            patch = 0
        # replace existing
        for i, s in enumerate(self.syms):
            if s["addr"] == addr:
                s["text"] = text
                s["patch"] = patch
                return i
        self.syms.append({"addr": addr, "text": text, "patch": patch, "original": 0})
        return len(self.syms) - 1

    def find_symbol_name(self, addr: int) -> str:
        addr &= ADDRMASK_UH
        best = None
        best_a = -1
        for s in self.syms:
            if s["addr"] == addr:
                return s["text"]
            if best_a < s["addr"] <= addr:
                best_a = s["addr"]
                best = s
        if best is None:
            return "?"
        off = addr - best["addr"]
        if off > 99999:
            return "?"
        if off == 0:
            return best["text"]
        return f"?{off}+{best['text']}"

    def routine_crc2(self, addr: int, crc1_in: int) -> Tuple[int, int]:
        """UltraHLE routinecrc2(addr, barrier=0) — CRC test against known crc1."""
        crc1 = crc1_in
        crc2 = 0
        x1 = self._rd32(addr)
        if not (x1 & 0xFFFFFF):
            return (-1, -1)
        inn = 16
        for i in range(16):
            x1 = self._rd32(addr + i * 4)
            if x1 == 0x03E00008:  # JR RA
                inn = min(i + 2, 16)
                break
        for i in range(inn):
            x1 = self._rd32(addr + i * 4)
            crc = i
            op = _uh_op_op(x1)
            if op in (2, 3):  # J / JAL
                crc += op
            elif op == 15:  # LUI
                imm = _uh_op_imm(x1)
                if 0xA400 <= imm <= 0xAFFF:
                    crc2 = u32(crc2 + x1)
                else:
                    crc += op
            elif op == 16 or op == 17:  # COP0 / COP1
                crc2 ^= x1
                crc = 0
            else:
                if crc1 & (1 << i):
                    crc ^= (x1 >> 16)
                else:
                    crc ^= x1
            x1 = crc
            if inn < 4:
                x1 ^= (x1 >> 16)
                x1 ^= (x1 >> 8)
                x1 = (x1 & 255) << (i * 8)
            elif inn < 8:
                x1 ^= (x1 >> 16)
                x1 ^= (x1 >> 8)
                x1 ^= (x1 >> 4)
                x1 = (x1 & 15) << (i * 4)
            else:
                x1 ^= (x1 >> 16)
                x1 ^= (x1 >> 8)
                x1 ^= (x1 >> 4)
                x1 ^= (x1 >> 2)
                x1 = (x1 & 3) << (i * 2)
            crc2 ^= x1
        return (crc1, u32(crc2))

    def patch_names(self):
        """Assign patch ids from ospatch[] patterns (sym_patchnames)."""
        patterns = []
        for entry in ULTRAHLE_OSPATCH:
            sp = entry.find(" ")
            if sp < 0:
                continue
            namepart = entry[:sp]
            wild = namepart.endswith("*")
            nlen = len(namepart) - (1 if wild else 0)
            hashp = entry.find("#")
            pnum = int(entry[hashp + 1:]) if hashp >= 0 else 0
            patterns.append((namepart[:nlen], wild, nlen, pnum, entry))
        for i, s in enumerate(list(self.syms)):
            text = s["text"]
            if "%" in text:
                continue
            if "#" in text and s["patch"]:
                continue
            if s["patch"]:
                continue
            base = text.split("#", 1)[0].strip()
            for npart, wild, nlen, pnum, _full in patterns:
                if len(base) < nlen:
                    continue
                if base[:nlen].lower() != npart.lower():
                    continue
                if not wild and len(base) > nlen and base[nlen] > " ":
                    continue
                self.add_symbol(s["addr"], f"{base} #{pnum}", pnum)
                break

    def find_os_calls(self, base: int, nbytes: int, cont: int = 0) -> str:
        """sym_findoscalls — scan memory for oscall[] signatures."""
        if nbytes <= 0:
            self.last_report = "empty range"
            return self.last_report
        base = u32(base | 0x80000000)
        end = u32(base + nbytes)
        # Working copy of oscall state
        state = []
        for data, crc1, crc2, patch, name in ULTRAHLE_OSCALL:
            state.append({
                "data": data, "crc1": crc1, "crc2": crc2, "patch": patch, "name": name,
                "flag": 0, "symb": 0, "found_at": 0, "fclass": 0,
            })
        total = len(state)
        for i in range(end - 4, base - 1, -4):
            x0 = self._rd32(i)
            if not (x0 & 0xFFFFFF):
                continue
            hits = []
            for j, e in enumerate(state):
                if e["found_at"]:
                    continue
                d0 = e["data"][0]
                if d0 and ((x0 ^ d0) >> 16):
                    continue
                ok = True
                for k in range(1, 8):
                    x = self._rd32(i + k * 4)
                    y = e["data"][k]
                    if y and ((x ^ y) >> 16):
                        ok = False
                        break
                if not ok:
                    continue
                if not e["symb"]:
                    e["symb"] = i
                e["flag"] = 1
                hits.append(j)
            if not hits:
                continue
            if self.find_symbol_name(i) != "?":
                for j in hits:
                    state[j]["flag"] = 0
                continue
            found = 0
            class_ = 0
            cnt16 = 0
            for j in hits:
                e = state[j]
                _c1, y = self.routine_crc2(i, e["crc1"])
                cl = 0
                if e["crc2"] == y:
                    cl = 16
                else:
                    yy = y ^ e["crc2"]
                    for k in range(0, 32, 2):
                        if not (yy & (3 << k)):
                            cl += 1
                if cl > class_:
                    class_ = cl
                    if class_ == 16:
                        cnt16 += 1
                    found = j
                    e["flag"] = 2
                else:
                    e["flag"] = 1
            if class_ > 8:
                j = found
                if cnt16 > 1:
                    for jj in hits:
                        if state[jj]["flag"] == 2 and not state[jj]["fclass"]:
                            j = jj
                            break
                e = state[j]
                e["fclass"] = class_
                e["found_at"] = i
                e["symb"] = self.add_symbol(i, e["name"], e["patch"])
                self.found[i] = {"name": e["name"], "patch": e["patch"], "class": class_}
                nm = e["name"]
                if "EnqueueAndYield" in nm or "YieldThread" in nm:
                    self.yield_addrs.add(u32(i | 0x80000000))

            for j in hits:
                state[j]["flag"] = 0
        self.patch_names()
        cnt = sum(1 for e in state if e["found_at"])
        important = sum(1 for e in state if e["patch"] >= 10)
        imp_found = sum(1 for e in state if e["found_at"] and e["patch"] >= 10)
        self.last_report = f"OS-routine search: {cnt}/{total} found, {imp_found}/{important} important"
        return self.last_report

    def add_patches(self) -> int:
        """sym_addpatches — write PATCH(id) over every patched symbol."""
        n = 0
        first = 0xFFFFFFFF
        last = 0
        for s in self.syms:
            patch = s["patch"]
            if not patch:
                continue
            addr = s["addr"] | 0x80000000
            old = self._rd32(addr)
            if _uh_op_op(old) != ULTRAHLE_OP_PATCH:
                s["original"] = old
            self._wr32(addr, make_ultrahle_patch(patch))
            n += 1
            a = addr & ADDRMASK_UH
            if a < first:
                first = a
            if a > last:
                last = a
        self.patches_applied = n
        self.first_patch = 0 if first == 0xFFFFFFFF else first
        self.last_patch = last
        return n

    def find_first_os(self) -> str:
        if self.osrange[0] and self.osrange[1] and self.osrange[1] > self.osrange[0]:
            report = self.find_os_calls(self.osrange[0], self.osrange[1] - self.osrange[0], 0)
        else:
            # Unknown commercial title: scan a wide KSEG0 window for libultra.
            report = self.find_os_calls(0x80000000, 0x200000, 0)
        # If the profile range missed the OS, fall back to a broad rescan.
        if len(self.found) < 8 and self.osrange[0]:
            extra = self.find_os_calls(0x80000000, 0x200000, 0)
            report = f"{report}; fallback={extra}"
        return report

    def apply_game_profile(self, title: str):
        prof = ultrahle_match_ini(title)
        self.ismario = int(prof.get("ismario", 0))
        self.iszelda = int(prof.get("iszelda", 0))
        self.bootloader = int(prof.get("bootloader", 0))
        self.ini_patches = list(prof.get("patches", []))
        if "osrange" in prof:
            self.osrange = tuple(prof["osrange"])  # type: ignore
        t = (title or "").upper()
        if t.startswith("SUPER MARIO"):
            self.ismario = 1
            if not self.osrange[0]:
                self.osrange = (0x80300000, 0x80380000)
        if t.startswith("THE LEGEND") or "ZELDA" in t:
            self.iszelda = 1
        if "BANJO" in t or t.startswith("F-ZERO"):
            self.bootloader = 1

    def apply_ini_patches(self, dma_num: int = 0) -> int:
        """Port of UltraHLE inifile_patches(dmanum) for boot-time / every-frame patches."""
        n = 0
        bus = self.core.bus
        for when, addr, kind, data in self.ini_patches:
            if when != dma_num and when != -1:
                continue
            addr = u32(addr)
            kind = str(kind).lower()
            if kind == "patch":
                bus.write_u32(addr, make_ultrahle_patch(int(data)))
                n += 1
            elif kind == "word":
                bus.write_u32(addr, u32(data))
                n += 1
            elif kind == "byte":
                bus.write_u8(addr, u32(data) & 0xFF)
                n += 1
        return n

    def boot_scan_and_patch(self, title: str, codebase: int) -> str:
        self.reset()
        self.codebase = u32(codebase)
        self.apply_game_profile(title)
        report = self.find_first_os()
        n = self.add_patches()
        ini_n = self.apply_ini_patches(0)
        report = (
            f"{report}; patches={n} ini={ini_n} "
            f"flags=m{self.ismario}z{self.iszelda}b{self.bootloader} "
            f"range={self.first_patch:08X}..{self.last_patch:08X}"
        )
        self.last_report = report
        return report



def _h_PATCH(cpu, o, old_pc, g):
    """UltraHLE OP_PATCH — HLE a libultra OS routine, then return to RA."""
    patch = o.imm & 0xFFFF
    # Banjo special-case: continue at pc+4 instead of returning (PATCH.C p_banjojalr).
    if patch == 49:
        fn = ULTRAHLE_PATCH_TABLE.get(49)
        if fn: fn(cpu.core.ultrahle, cpu, g)
        return
    if patch <= 2:
        # __osEnqueueAndYield / DispatchThread were mapped to skip(#1) in UltraHLE,
        # but a pure return spins; perform a real yield into another ready thread.
        if patch == 1 and old_pc in getattr(cpu.core.uh_sym, "yield_addrs", ()):
            hle = cpu.core.ultrahle
            cur = hle.threads.get(hle.current_thread)
            if cur is not None:
                ra = u32(g[_UH_RA])
                cur["pc"] = ra
                cur["next_pc"] = u32(ra + 4)
                cur["gpr"] = list(cpu.gpr)
                cur["hi"] = cpu.hi
                cur["lo"] = cpu.lo
            if hle.schedule(0):
                return
        ra = u32(g[_UH_RA])
        cpu.pc = ra
        cpu.next_pc = u32(ra + 4)
        return
    # Stash PATCH address so blocking handlers can rewind before schedule/_save.
    cpu._patch_pc = u32(old_pc)
    fn = ULTRAHLE_PATCH_TABLE.get(patch)
    blocked = None
    if fn is not None:
        blocked = fn(cpu.core.ultrahle, cpu, g)
    if blocked == "switched":
        # Thread switch already loaded PC/GPRs — do not return to RA.
        return
    if blocked == "block":
        # Stay on the PATCH opcode (UltraHLE blocktask rewinds PC).
        cpu.pc = u32(old_pc)
        cpu.next_pc = u32(old_pc + 4)
        hle = cpu.core.ultrahle
        cur = hle.threads.get(hle.current_thread)
        if cur is not None:
            cur["pc"] = u32(old_pc)
            cur["next_pc"] = u32(old_pc + 4)
            cur["gpr"] = list(cpu.gpr)
            cur["hi"] = cpu.hi
            cur["lo"] = cpu.lo
        return
    # Default UltraHLE PATCHRET: return to caller immediately.
    ra = u32(g[_UH_RA])
    cpu.pc = ra
    cpu.next_pc = u32(ra + 4)
    # Deferred preempt: switch to a higher-pri thread woken during this PATCH.
    cpu.core.ultrahle.maybe_preempt()

def _h_GROUP(cpu, o, old_pc, g):
    """UltraHLE OP_GROUP — dynarec group marker; no-op in the interpreter."""
    pass

def _h_CACHE(cpu, o, old_pc, g): pass
def _h_SYNC(cpu, o, old_pc, g): pass
def _h_WAIT(cpu, o, old_pc, g): pass
def _h_RI(cpu, o, old_pc, g):
    cpu._raise_exception(10, old_pc)  # Reserved Instruction
def _h_CPU_UNUSABLE(cpu, o, old_pc, g):
    cpu._raise_exception(11, old_pc)  # Coprocessor Unusable (COP2/COP3)


# PRIMARY
for _op,_fn in [
    (0x02,_h_J),(0x03,_h_JAL),(0x04,_h_BEQ),(0x05,_h_BNE),(0x06,_h_BLEZ),(0x07,_h_BGTZ),
    (0x08,_h_ADDI),(0x09,_h_ADDIU),(0x0A,_h_SLTI),(0x0B,_h_SLTIU),(0x0C,_h_ANDI),(0x0D,_h_ORI),(0x0E,_h_XORI),(0x0F,_h_LUI),
    (0x14,_h_BEQL),(0x15,_h_BNEL),(0x16,_h_BLEZL),(0x17,_h_BGTZL),
    (0x18,_h_DADDI),(0x19,_h_DADDIU),(0x1A,_h_LDL),(0x1B,_h_LDR),
    (0x1C,_h_PATCH),(0x1D,_h_GROUP),
    (0x20,_h_LB),(0x21,_h_LH),(0x22,_h_LWL),(0x23,_h_LW),(0x24,_h_LBU),(0x25,_h_LHU),(0x26,_h_LWR),(0x27,_h_LWU),
    (0x28,_h_SB),(0x29,_h_SH),(0x2A,_h_SWL),(0x2B,_h_SW),(0x2C,_h_SDL),(0x2D,_h_SDR),(0x2E,_h_SWR),(0x2F,_h_CACHE),
    (0x30,_h_LL),(0x31,_h_LWC1),(0x32,_h_NOP),(0x33,_h_NOP),(0x34,_h_LLD),(0x35,_h_LDC1),(0x36,_h_NOP),(0x37,_h_LD),
    (0x38,_h_SC),(0x39,_h_SWC1),(0x3A,_h_NOP),(0x3B,_h_NOP),(0x3C,_h_SCD),(0x3D,_h_SDC1),(0x3E,_h_NOP),(0x3F,_h_SD),
]: _DISPATCH[_ID_PRIMARY|_op] = _fn
# SPECIAL
for _f,_fn in [
    (0x00,_h_SLL),(0x02,_h_SRL),(0x03,_h_SRA),(0x04,_h_SLLV),(0x06,_h_SRLV),(0x07,_h_SRAV),
    (0x08,_h_JR),(0x09,_h_JALR),(0x0A,_h_MOVZ),(0x0B,_h_MOVN),(0x0C,_h_SYSCALL),(0x0D,_h_BREAK),(0x0F,_h_SYNC),
    (0x10,_h_MFHI),(0x11,_h_MTHI),(0x12,_h_MFLO),(0x13,_h_MTLO),
    (0x14,_h_DSLLV),(0x16,_h_DSRLV),(0x17,_h_DSRAV),
    (0x18,_h_MULT),(0x19,_h_MULTU),(0x1A,_h_DIV),(0x1B,_h_DIVU),(0x1C,_h_DMULT),(0x1D,_h_DMULTU),(0x1E,_h_DDIV),(0x1F,_h_DDIVU),
    (0x20,_h_ADD),(0x21,_h_ADDU),(0x22,_h_SUB),(0x23,_h_SUBU),(0x24,_h_AND),(0x25,_h_OR),(0x26,_h_XOR),(0x27,_h_NOR),
    (0x2A,_h_SLT),(0x2B,_h_SLTU),(0x2C,_h_DADD),(0x2D,_h_DADDU),(0x2E,_h_DSUB),(0x2F,_h_DSUBU),
    (0x30,_h_TGE),(0x31,_h_TGEU),(0x32,_h_TLT),(0x33,_h_TLTU),(0x34,_h_TEQ),(0x36,_h_TNE),
    (0x38,_h_DSLL),(0x3A,_h_DSRL),(0x3B,_h_DSRA),(0x3C,_h_DSLL32),(0x3E,_h_DSRL32),(0x3F,_h_DSRA32),
]: _DISPATCH[_ID_SPECIAL|_f] = _fn
for _f in (0x01,0x05,0x0E,0x15,0x28,0x29,0x35,0x37,0x39,0x3D):
    _DISPATCH[_ID_SPECIAL|_f] = _h_RI
# REGIMM
for _rt,_fn in [
    (0x00,_h_BLTZ),(0x01,_h_BGEZ),(0x02,_h_BLTZL),(0x03,_h_BGEZL),
    (0x08,_h_TGEI),(0x09,_h_TGEIU),(0x0A,_h_TLTI),(0x0B,_h_TLTIU),(0x0C,_h_TEQI),(0x0E,_h_TNEI),
    (0x10,_h_BLTZAL),(0x11,_h_BGEZAL),(0x12,_h_BLTZALL),(0x13,_h_BGEZALL),
]: _DISPATCH[_ID_REGIMM|_rt] = _fn
for _rt in (0x04,0x05,0x06,0x07,0x0D,0x0F):
    _DISPATCH[_ID_REGIMM|_rt] = _h_RI
for _rt in range(0x14, 0x20):
    _DISPATCH[_ID_REGIMM|_rt] = _h_RI
# COP0_RS
for _rs,_fn in [
    (0x00,_h_MFC0),(0x01,_h_DMFC0),(0x02,_h_CFC0),(0x04,_h_MTC0),(0x05,_h_DMTC0),(0x06,_h_CTC0),(0x08,_h_BC0),
]: _DISPATCH[_ID_COP0_RS|_rs] = _fn
# COP0_CO
for _cof,_fn in [
    (0x01,_h_TLBR),(0x02,_h_TLBWI),(0x06,_h_TLBWR),(0x08,_h_TLBP),(0x18,_h_ERET),
]: _DISPATCH[_ID_COP0_CO|_cof] = _fn
_DISPATCH[_ID_COP0_CO|0x20] = _h_WAIT
for _cof in (0x00,0x03,0x04,0x05,0x07):
    _DISPATCH[_ID_COP0_CO|_cof] = _h_RI
# COP1_RS
for _rs,_fn in [
    (0x00,_h_MFC1),(0x01,_h_DMFC1),(0x02,_h_CFC1),(0x04,_h_MTC1),(0x05,_h_DMTC1),(0x06,_h_CTC1),(0x08,_h_BC1),
]: _DISPATCH[_ID_COP1_RS|_rs] = _fn
# BC1F/BC1T/BC1FL/BC1TL use _ID_COP1_BC|rt (critical for FPU branches)
for _rt in range(32):
    _DISPATCH[_ID_COP1_BC|_rt] = _h_BC1
# FPU (all format+funct combos go to _h_FPU)
for _fid in (_ID_FPU_S,_ID_FPU_D,_ID_FPU_W,_ID_FPU_L):
    for _f in range(64):
        _DISPATCH[_ID_FPU|(_fid<<6)|_f] = _h_FPU
# COP2/COP3 + reserved primary ops
for _op in (0x12, 0x13):
    _DISPATCH[_ID_PRIMARY|_op] = _h_CPU_UNUSABLE
for _op in (0x1E, 0x1F):
    _DISPATCH[_ID_PRIMARY|_op] = _h_RI
# LWC2/SWC2/LDC2/SDC2/LWC3/SWC3 are unused on VR4300 CPU — RI
for _op in (0x32, 0x33, 0x36, 0x3A, 0x3B, 0x3E):
    _DISPATCH[_ID_PRIMARY|_op] = _h_RI


# ── ACsN64Core — full emulator core ──
class ACsN64Core:
    def __init__(self):
        self.rdram = bytearray(RDRAM_SIZE)
        self.rom = bytearray()
        self.rom_path = ""
        self.rom_header:Optional[N64Header]=None
        self.cic = CIC_NUS_6102
        self.pif_ram = bytearray(PIF_RAM_SIZE)
        self.rsp_dmem = bytearray(RSP_DMEM_SIZE)
        self.rsp_imem = bytearray(RSP_IMEM_SIZE)
        self.rsp_pc = 0
        self.audio_signal = False
        self._vi_origin_set = False
        self.save_mgr = SaveManager()
        self.cheat_engine = CheatEngine()
        self.cpu = CPUCore(self)
        self.bus = DeviceBus(self)
        self.ultrahle = UltraHleOs(self)
        self.uh_sym = UltraHleSym(self)
        self.uh_boot_report = ""
        self.running = False
        self.frame_count = 0
        self.vi_counter = 0
        self.cycle_count = 0
        self.vi_clock = 48682
        self.cycles_per_frame = N64_CYCLES_PER_FRAME_NTSC
        self.frame_period = FRAME_PERIOD_NTSC
        self.cycle_limit = INTERP_MAX_STEPS
        self.interp_steps = 40_000
        self.fb_ppm:Optional[bytes]=None
        self.fb_lit = False
        self.boot_turbo = True
        self.last_os_task = 0
        self._rdp_reset_state()
        self.reset()

    def _rdp_reset_state(self):
        self.rdp_fill_color = 0
        self.rdp_color_img = 0
        self.rdp_color_width = 320
        self.rdp_segments = [0] * 16
        self.rdp_verts = [
            {"x": 0.0, "y": 0.0, "z": 0.0, "w": 1.0, "r": 0, "g": 0, "b": 0, "a": 0}
            for _ in range(32)
        ]
        ident = [[1.0 if i == j else 0.0 for j in range(4)] for i in range(4)]
        self.rdp_modelview = [row[:] for row in ident]
        self.rdp_projection = [row[:] for row in ident]
        self.rdp_mv_stack: list = []
        self.rdp_vp_scale = [160.0, 120.0, 511.0, 0.0]
        self.rdp_vp_trans = [160.0, 120.0, 511.0, 0.0]

    def reset(self):
        self.rdram = bytearray(RDRAM_SIZE)
        self.rsp_dmem = bytearray(RSP_DMEM_SIZE)
        self.rsp_imem = bytearray(RSP_IMEM_SIZE)
        self._vi_origin_set = False
        self.vi_counter = 0
        self.frame_count = 0
        self.fb_ppm = None
        self.fb_lit = False
        self.boot_turbo = True
        self.last_os_task = 0
        self._rdp_reset_state()
        seed_pif_ram(self.pif_ram, self.cic)
        self.cpu.reset()
        self.bus.reset()
        self.save_mgr.reset()
        self.ultrahle.reset()
        self.uh_sym.reset()
        self.uh_boot_report = ""

    def load_rom(self, path):
        try:
            with open(path, "rb") as f:
                raw = bytearray(f.read())
        except Exception as e:
            return str(e)
        if len(raw) < 0x40:
            return "ROM too small (<64 bytes)"
        norm = normalize_rom_bytes(raw)
        self.rom = bytearray(norm)
        self.rom_path = path
        self.cic = get_cic_chip_id(self.rom)
        self.rom_header = N64Header(self.rom)
        seed_pif_ram(self.pif_ram, self.cic)
        dst = get_rom_region(self.rom)
        if dst == REGION_NTSC:
            self.vi_clock = 48682
            self.cycles_per_frame = N64_CYCLES_PER_FRAME_NTSC
            self.frame_period = FRAME_PERIOD_NTSC
        else:
            self.vi_clock = 49665
            self.cycles_per_frame = N64_CYCLES_PER_FRAME_PAL
            self.frame_period = FRAME_PERIOD_PAL
        self.cycle_limit = INTERP_MAX_STEPS
        self.interp_steps = INTERP_BOOT_STEPS
        self.fb_lit = False
        self.boot_turbo = True
        self.reset()
        self.bus.regs[PI_STATUS] = 0
        self.bus.hw_interrupts = 0
        self._hle_ipl3_boot()
        return None

    def _hle_ipl3_boot(self):
        """Skip real IPL3: seed GPRs like commercial CIC boot, DMA cart→RDRAM, jump to entry.

        Real IPL3 DMAs cartridge bytes from 0x1000 into RDRAM at (boot_address & 0x1FFFFFFF).
        CIC 6103/6106 subtract 0x100000/0x200000 from the header entry before jump+DMA.
        """
        rom = self.rom
        # Cart image at SP DMEM during PIF boot (first 0x1000 bytes = header + IPL3).
        head = rom[:0x1000] if len(rom) >= 0x1000 else rom + bytes(0x1000 - len(rom))
        self.rsp_dmem[:] = bytearray(head[:0x1000])
        if len(self.rsp_imem) >= 0x1000:
            self.rsp_imem[:] = bytearray(head[:0x1000])

        entry = normalize_commercial_entry(
            self.rom_header.boot_address if self.rom_header else 0x80000400
        )
        cic = self.cic
        if cic == CIC_NUS_6103:
            entry = u32(entry - 0x100000)
        elif cic == CIC_NUS_6106:
            entry = u32(entry - 0x200000)
        # UltraHLE boot.c: alternate bootloader (Banjo/F-Zero) clears codebase bits.
        title = ""
        if self.rom_header is not None:
            title = getattr(self.rom_header, "title", "") or ""
        prof = ultrahle_match_ini(title)
        bootloader = int(prof.get("bootloader", 0))
        if len(rom) > 0x544 and be32(rom, 0x540) != 0:
            bootloader = 1
        if bootloader:
            entry = u32(entry & ~0x300000)
        entry_phys = entry & 0x1FFFFFFF
        # Clear RDRAM then perform the IPL3 cart DMA (cart+0x1000 → RDRAM@entry).
        self.rdram[:] = bytearray(RDRAM_SIZE)
        if len(rom) > 0x1000 and entry_phys < RDRAM_SIZE:
            src = memoryview(rom)[0x1000:]
            n = min(len(src), RDRAM_SIZE - entry_phys)
            self.rdram[entry_phys:entry_phys + n] = src[:n]

        cpu = self.cpu
        g = cpu.gpr
        for i in range(32):
            g[i] = 0
        # Common post-IPL3 register seed (mupen/Project64 HLE-compatible).
        g[1] = 0x0000000000000001
        g[6] = 0xFFFFFFFFA4001F0C
        g[7] = 0xFFFFFFFFA4001F08
        g[8] = 0x00000000000000C0
        g[10] = 0x0000000000000040
        g[11] = 0xFFFFFFFFA4000040
        g[29] = 0xFFFFFFFFA4001FF0
        if cic == CIC_NUS_6101:
            g[22] = 0x000000000000003F
            g[5] = 0xFFFFFFFFC0F1D859
            g[14] = 0x000000002DE108EA
        elif cic == CIC_NUS_6102:
            g[22] = 0x000000000000003F
            g[5] = 0xFFFFFFFFC0F1D859
            g[14] = 0x000000002DE108EA
        elif cic == CIC_NUS_6103:
            g[22] = 0x0000000000000078
            g[5] = 0xFFFFFFFFD4646273
            g[14] = 0x000000001AF53600
        elif cic == CIC_NUS_6105:
            g[22] = 0x0000000000000091
            g[5] = 0xFFFFFFFFDECAAAD1
            g[14] = 0x000000000CF85C13
        elif cic == CIC_NUS_6106:
            g[22] = 0x0000000000000085
            g[5] = 0xFFFFFFFFB04DC903
            g[14] = 0x000000001AF53600
        else:
            g[22] = 0x000000000000003F
        g[20] = 0x0000000000000001
        g[23] = 0x0000000000000000
        g[24] = 0x0000000000000003
        g[31] = 0xFFFFFFFFA4001550
        cpu.hi = 0; cpu.lo = 0
        cpu.llbit = False; cpu.lladdr = 0
        cpu.cp0[CP0_STATUS] = 0x34000000 | STATUS_CU1
        cpu.cp0[CP0_CONFIG] = 0x7006E463
        cpu.cp0[CP0_COUNT] = 0x5000
        cpu.cp0[CP0_CAUSE] = 0x5C
        cpu.cp0[CP0_CONTEXT] = 0x007FFFF0
        cpu.cp0[CP0_EPC] = 0xFFFFFFFF
        cpu.cp0[CP0_BADVADDR] = 0xFFFFFFFF
        cpu.cp0[CP0_ERROREPC] = 0xFFFFFFFF
        cpu.cp0[CP0_COMPARE] = 0xFFFFFFFF
        cpu.cp0[CP0_PRID] = 0x00000B00
        cpu.pc = entry
        cpu.next_pc = u32(entry + 4)
        self.save_mgr.save_type = detect_save_type(rom)
        self.ultrahle.reset()
        self.bus.hw_interrupts = 0
        self.bus.mi_intr_mask = 0
        self.bus.sp_status = SP_STATUS_HALT
        self._vi_origin_set = False
        # UltraHLE boot.c: sym_findfirstos + sym_addpatches after cart DMA.
        self.uh_boot_report = self.uh_sym.boot_scan_and_patch(title, entry)
        self.ultrahle.ismario = self.uh_sym.ismario
        self.ultrahle.iszelda = self.uh_sym.iszelda
        self.ultrahle.bootloader = self.uh_sym.bootloader or bootloader
        if self.ultrahle.ismario:
            self.rdp_ucode = "f3d"
        elif self.ultrahle.iszelda:
            self.rdp_ucode = "f3dex2"


    def trigger_sp_dma(self, to_rsp:bool):
        sp_mem = self.bus.regs.get(SP_MEM_ADDR, 0) & 0xFFF
        dram = self.bus.regs.get(SP_DRAM_ADDR, 0) & 0x00FFFFFF
        length = self.bus.regs.get(SP_RD_LEN if to_rsp else SP_WR_LEN, 0) & 0xFFF
        if length == 0:
            length = 8
        if to_rsp:
            src = dram + 0 if dram < RDRAM_SIZE else 0
            dst = sp_mem
            data = self.rdram[src:src+length] if src+length <= RDRAM_SIZE else bytearray(length)
            if 0 <= dst < RSP_DMEM_SIZE:
                end = min(dst+length, RSP_DMEM_SIZE)
                self.rsp_dmem[dst:end] = data[:end-dst]
            elif RSP_DMEM_SIZE <= dst < RSP_DMEM_SIZE+RSP_IMEM_SIZE:
                off = dst - RSP_DMEM_SIZE
                end = min(off+length, RSP_IMEM_SIZE)
                self.rsp_imem[off:end] = data[:end-off]
        else:
            dst = dram if dram < RDRAM_SIZE else 0
            src = sp_mem
            if 0 <= src < RSP_DMEM_SIZE:
                data = self.rsp_dmem[src:src+length]
            elif RSP_DMEM_SIZE <= src < RSP_DMEM_SIZE+RSP_IMEM_SIZE:
                off = src - RSP_DMEM_SIZE
                data = self.rsp_imem[off:off+length]
            else:
                data = bytearray(length)
            end = min(dst+length, RDRAM_SIZE)
            self.rdram[dst:end] = data[:end-dst]
        self.bus.hw_interrupts |= MI_INTR_SP

    def trigger_pi_dma(self):
        """PI DMA — note N64 naming: WR_LEN = cart→RDRAM, RD_LEN = RDRAM→cart."""
        dram = self.bus.regs.get(PI_DRAM_ADDR, 0) & 0x00FFFFFF
        cart = self.bus.regs.get(PI_CART_ADDR, 0) & MASK_32
        rdlen = self.bus.regs.get(PI_RD_LEN, 0) & 0x00FFFFFF
        wrlen = self.bus.regs.get(PI_WR_LEN, 0) & 0x00FFFFFF
        # Hardware: writing PI_WR_LEN starts cart→RDRAM; PI_RD_LEN starts RDRAM→cart.
        cart_to_rdram = wrlen > 0 or rdlen == 0
        length = wrlen if wrlen > 0 else rdlen
        if length == 0:
            length = 64
        length = (length & 0x00FFFFFE) + 1
        ca = cart & 0x1FFFFFFF
        # Accept bare cart offsets (UltraHLE / libultra often pass ROM-relative addrs).
        if ca < 0x04000000:
            ca = 0x10000000 + ca
            cart = ca
        if cart_to_rdram:
            if 0x10000000 <= ca < 0x10000000 + len(self.rom):
                off = ca - 0x10000000
                src = self.rom[off:off + length]
            elif 0x08000000 <= ca < 0x09000000:
                self.save_mgr.pi_read(ca, length, self.rdram, dram)
                src = self.rdram[dram:dram + length]
            else:
                src = bytearray(min(length, max(0, RDRAM_SIZE - dram)))
            end = min(dram + len(src), RDRAM_SIZE)
            if end > dram:
                self.rdram[dram:end] = src[: end - dram]
        else:
            self.save_mgr.pi_write(ca, length, self.rdram, dram)
        self.bus.regs[PI_WR_LEN] = 0
        self.bus.regs[PI_RD_LEN] = 0
        self.bus.hw_interrupts |= MI_INTR_PI

    def trigger_si_dma(self, read_pif:bool):
        dram = self.bus.regs.get(SI_DRAM_ADDR, 0) & 0x00FFFFFF
        if read_pif:
            self._pif_process_commands()
            for i in range(min(PIF_RAM_SIZE, RDRAM_SIZE - dram)):
                self.rdram[dram + i] = self.pif_ram[i]
        else:
            for i in range(min(PIF_RAM_SIZE, RDRAM_SIZE - dram)):
                self.pif_ram[i] = self.rdram[dram + i]
            self._pif_process_commands()
        self.bus.hw_interrupts |= MI_INTR_SI

    def _pif_process_commands(self):
        """Joybus HLE: controller on ch0 + EEPROM on ch4 when cart uses EEPROM."""
        pif = self.pif_ram
        sm = self.save_mgr
        i = 0
        channel = 0
        while i < PIF_RAM_SIZE - 1:
            cmd = pif[i]
            if cmd == 0xFE:  # end of commands
                break
            if cmd == 0xFF or cmd == 0x00:  # padding / skip channel
                if cmd == 0x00:
                    channel += 1
                i += 1
                continue
            if cmd == 0xFD:  # reset channel
                i += 1
                channel += 1
                continue
            t = pif[i]; r = pif[i + 1] if i + 1 < PIF_RAM_SIZE else 0
            if t == 0:
                i += 1
                continue
            # Standard N64 controller: tx=1 cmd, rx=3/4 status/buttons
            if i + 2 < PIF_RAM_SIZE:
                joy_cmd = pif[i + 2]
                if channel == 0:
                    if joy_cmd in (0x00, 0xFF) and r >= 3:
                        # Identify: standard controller with no pak
                        if i + 5 < PIF_RAM_SIZE:
                            pif[i + 3] = 0x05; pif[i + 4] = 0x00; pif[i + 5] = 0x02
                    elif joy_cmd == 0x01 and r >= 4:
                        # Controller state: buttons from HLE pad + stick center
                        if i + 6 < PIF_RAM_SIZE:
                            btn = self.ultrahle.cont_pad & 0xFFFF
                            pif[i + 3] = (btn >> 8) & 0xFF
                            pif[i + 4] = btn & 0xFF
                            pif[i + 5] = 0x00
                            pif[i + 6] = 0x00
                elif channel == 4 and sm.eeprom_present():
                    # Cartridge EEPROM (Joybus channel 4)
                    if joy_cmd in (0x00, 0xFF) and r >= 3:
                        typ = 0xC0 if sm.save_type == SAVE_EEPROM_16K else 0x80
                        if i + 5 < PIF_RAM_SIZE:
                            pif[i + 3] = 0x00; pif[i + 4] = typ; pif[i + 5] = 0x00
                    elif joy_cmd == 0x04 and t >= 2 and r >= 8:
                        # EEPROM read: addr = pif[i+3], 8 data bytes
                        block = pif[i + 3] if i + 3 < PIF_RAM_SIZE else 0
                        tmp = bytearray(EEPROM_BLOCK)
                        if sm.eeprom_read_block(block, tmp) == 0 and i + 11 < PIF_RAM_SIZE:
                            pif[i + 4:i + 12] = tmp
                    elif joy_cmd == 0x05 and t >= 10:
                        # EEPROM write: addr + 8 bytes
                        block = pif[i + 3] if i + 3 < PIF_RAM_SIZE else 0
                        if i + 12 <= PIF_RAM_SIZE:
                            sm.eeprom_write_block(block, pif, i + 4)
                            if r >= 1 and i + 3 + t < PIF_RAM_SIZE:
                                pif[i + 2 + t] = 0x00
                elif channel != 0:
                    # No device on other channels
                    pif[i + 1] |= 0x80
            i += 2 + t + (r & 0x3F)
            channel += 1
        pif[0x3F] = 0x00

    def process_rsp(self):
        """HLE RSP: complete OSTask, raise SP (and DP for graphics)."""
        bus = self.bus
        task = u32(getattr(self, "last_os_task", 0))
        task_type = 0
        if task:
            task_type = self.bus.read_u32(task)
            put_be32(self.rsp_dmem, 0xFC0, task_type)
        else:
            task_type = be32(self.rsp_dmem, 0xFC0) if len(self.rsp_dmem) >= 0xFC4 else 0
        bus.sp_status |= SP_STATUS_HALT | SP_STATUS_BROKE
        bus.sp_status &= ~(SP_STATUS_DMA_BUSY | SP_STATUS_DMA_FULL | SP_STATUS_IO_FULL)
        bus.hw_interrupts |= MI_INTR_SP
        # type 1 = graphics, 2 = audio (libultra OSTask)
        if task_type == 1:
            self.process_rdp()
        elif task_type == 2:
            self.process_audio()
        else:
            # Unknown / boot microcode — still retire the task so games continue.
            bus.hw_interrupts |= MI_INTR_DP

    def _rdp_seg_addr(self, addr: int) -> int:
        addr = u32(addr)
        seg = (addr >> 24) & 0xFF
        if seg < 16 and self.rdp_segments[seg]:
            return u32((self.rdp_segments[seg] & 0x1FFFFFFF) + (addr & 0x00FFFFFF)) | 0x80000000
        return addr

    @staticmethod
    def _rdp_mat_ident():
        return [[1.0 if i == j else 0.0 for j in range(4)] for i in range(4)]

    @staticmethod
    def _rdp_mat_mul(a, b):
        out = [[0.0] * 4 for _ in range(4)]
        for i in range(4):
            for j in range(4):
                out[i][j] = a[i][0] * b[0][j] + a[i][1] * b[1][j] + a[i][2] * b[2][j] + a[i][3] * b[3][j]
        return out

    def _rdp_load_mtx(self, addr: int):
        """Load Nintendo Mtx (s15.16 int/frac halves) into a 4x4 float matrix."""
        addr = self._rdp_seg_addr(addr)
        phys = addr & 0x1FFFFFFF
        m = [[0.0] * 4 for _ in range(4)]
        rdram = self.rdram
        for i in range(4):
            for j in range(4):
                off = phys + (i * 4 + j) * 2
                if off + 33 >= len(rdram):
                    return self._rdp_mat_ident()
                hi = struct.unpack_from(">h", rdram, off)[0]
                lo = struct.unpack_from(">H", rdram, off + 32)[0]
                m[i][j] = float(hi) + (lo / 65536.0)
        return m

    def _rdp_load_viewport(self, addr: int):
        addr = self._rdp_seg_addr(addr)
        phys = addr & 0x1FFFFFFF
        if phys + 16 > len(self.rdram):
            return
        vals = struct.unpack_from(">8h", self.rdram, phys)
        # Vp: vscale[4], vtrans[4] in 2-unit fixed; screen uses /4.
        self.rdp_vp_scale = [vals[0] / 4.0, vals[1] / 4.0, vals[2] / 4.0, vals[3] / 4.0]
        self.rdp_vp_trans = [vals[4] / 4.0, vals[5] / 4.0, vals[6] / 4.0, vals[7] / 4.0]

    def _rdp_xform_vertex(self, x: float, y: float, z: float):
        # Clip = V * ModelView * Projection (row-vector).
        mv = self.rdp_modelview
        pr = self.rdp_projection
        # First MV
        x1 = x * mv[0][0] + y * mv[1][0] + z * mv[2][0] + mv[3][0]
        y1 = x * mv[0][1] + y * mv[1][1] + z * mv[2][1] + mv[3][1]
        z1 = x * mv[0][2] + y * mv[1][2] + z * mv[2][2] + mv[3][2]
        w1 = x * mv[0][3] + y * mv[1][3] + z * mv[2][3] + mv[3][3]
        # Then Projection
        xc = x1 * pr[0][0] + y1 * pr[1][0] + z1 * pr[2][0] + w1 * pr[3][0]
        yc = x1 * pr[0][1] + y1 * pr[1][1] + z1 * pr[2][1] + w1 * pr[3][1]
        zc = x1 * pr[0][2] + y1 * pr[1][2] + z1 * pr[2][2] + w1 * pr[3][2]
        wc = x1 * pr[0][3] + y1 * pr[1][3] + z1 * pr[2][3] + w1 * pr[3][3]
        if abs(wc) < 1e-6:
            wc = 1e-6
        ox = (xc / wc) * self.rdp_vp_scale[0] + self.rdp_vp_trans[0]
        oy = (yc / wc) * self.rdp_vp_scale[1] + self.rdp_vp_trans[1]
        return ox, oy, zc / wc, wc

    def _rdp_fill_rect(self, x0: int, y0: int, x1: int, y1: int):
        """Write RGB5551 fill color into the current color image."""
        img = u32(self.rdp_color_img) & 0x1FFFFFFF
        width = max(1, int(self.rdp_color_width) & 0xFFF)
        if width > 640:
            width = 320
        if x1 <= x0 or y1 <= y0:
            return
        x0 = max(0, min(width, x0)); x1 = max(0, min(width, x1))
        y0 = max(0, y0); y1 = max(0, y1)
        color = u32(self.rdp_fill_color)
        # Fill color is 32-bit with two 16-bit pixels; use the high half (common for 16bpp).
        px = (color >> 16) & 0xFFFF
        hi = (px >> 8) & 0xFF
        lo = px & 0xFF
        rdram = self.rdram
        stride = width * 2
        for y in range(y0, y1):
            row = img + y * stride
            if row < 0 or row + (x1 * 2) > len(rdram):
                break
            for x in range(x0, x1):
                off = row + x * 2
                rdram[off] = hi
                rdram[off + 1] = lo

    def _rdp_put_rgb5551(self, x: int, y: int, r: int, g: int, b: int):
        img = u32(self.rdp_color_img) & 0x1FFFFFFF
        width = max(1, int(self.rdp_color_width) & 0xFFF)
        if width > 640:
            width = 320
        if x < 0 or y < 0 or x >= width or y >= 240:
            return
        off = img + (y * width + x) * 2
        if off < 0 or off + 1 >= len(self.rdram):
            return
        pix = ((r & 0xF8) << 8) | ((g & 0xF8) << 3) | ((b & 0xF8) >> 2) | 1
        self.rdram[off] = (pix >> 8) & 0xFF
        self.rdram[off + 1] = pix & 0xFF

    def _rdp_draw_tri(self, i0: int, i1: int, i2: int):
        """Flat-shaded screen-space triangle using averaged vertex colors."""
        vs = self.rdp_verts
        if not (0 <= i0 < 32 and 0 <= i1 < 32 and 0 <= i2 < 32):
            return
        a, b, c = vs[i0], vs[i1], vs[i2]
        # Skip degenerate / behind-camera tris.
        if a["w"] <= 0 or b["w"] <= 0 or c["w"] <= 0:
            return
        x0, y0 = a["x"], a["y"]
        x1, y1 = b["x"], b["y"]
        x2, y2 = c["x"], c["y"]
        area = (x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0)
        if abs(area) < 1e-3:
            return
        r = (a["r"] + b["r"] + c["r"]) // 3
        g = (a["g"] + b["g"] + c["g"]) // 3
        bl = (a["b"] + b["b"] + c["b"]) // 3
        min_x = max(0, int(min(x0, x1, x2)))
        max_x = min(int(self.rdp_color_width) - 1, int(max(x0, x1, x2)))
        min_y = max(0, int(min(y0, y1, y2)))
        max_y = min(239, int(max(y0, y1, y2)))
        if min_x > max_x or min_y > max_y:
            return
        for y in range(min_y, max_y + 1):
            for x in range(min_x, max_x + 1):
                w0 = (x1 - x0) * (y - y0) - (y1 - y0) * (x - x0)
                w1 = (x2 - x1) * (y - y1) - (y2 - y1) * (x - x1)
                w2 = (x0 - x2) * (y - y2) - (y0 - y2) * (x - x2)
                if area > 0:
                    if w0 >= 0 and w1 >= 0 and w2 >= 0:
                        self._rdp_put_rgb5551(x, y, r, g, bl)
                else:
                    if w0 <= 0 and w1 <= 0 and w2 <= 0:
                        self._rdp_put_rgb5551(x, y, r, g, bl)

    def _rdp_sp_vertex(self, addr: int, n: int, v0: int):
        addr = self._rdp_seg_addr(addr)
        phys = addr & 0x1FFFFFFF
        n = max(0, min(32, n))
        v0 = max(0, min(31, v0))
        for i in range(n):
            dst = v0 + i
            if dst >= 32:
                break
            off = phys + i * 16
            if off + 16 > len(self.rdram):
                break
            x, y, z, _flag, _s, _t = struct.unpack_from(">hhhHhh", self.rdram, off)
            r, g, b, a = self.rdram[off + 12], self.rdram[off + 13], self.rdram[off + 14], self.rdram[off + 15]
            sx, sy, sz, sw = self._rdp_xform_vertex(float(x), float(y), float(z))
            self.rdp_verts[dst] = {"x": sx, "y": sy, "z": sz, "w": sw, "r": r, "g": g, "b": b, "a": a}

    def _rdp_apply_mtx(self, mat, params: int):
        is_proj = bool(params & 0x04)
        do_load = bool(params & 0x02)
        no_push = bool(params & 0x01)
        if is_proj:
            if do_load:
                self.rdp_projection = mat
            else:
                self.rdp_projection = self._rdp_mat_mul(mat, self.rdp_projection)
        else:
            if not no_push:
                self.rdp_mv_stack.append([row[:] for row in self.rdp_modelview])
                if len(self.rdp_mv_stack) > 16:
                    self.rdp_mv_stack.pop(0)
            if do_load:
                self.rdp_modelview = mat
            else:
                self.rdp_modelview = self._rdp_mat_mul(mat, self.rdp_modelview)

    def _rdp_texrect(self, x0: int, y0: int, x1: int, y1: int):
        """Fill a texture rectangle with the current fill color (soft approx)."""
        self._rdp_fill_rect(min(x0, x1), min(y0, y1), max(x0, x1) + 1, max(y0, y1) + 1)

    def _rdp_detect_ucode(self, dl: int) -> str:
        """Heuristic: Fast3D (SM64) vs F3DEX2 from early display-list opcodes."""
        # Prefer INI/title flags when UltraHLE would force them.
        if getattr(self.ultrahle, "ismario", 0):
            prefer = "f3d"
        elif getattr(self.ultrahle, "iszelda", 0):
            prefer = "f3dex2"
        else:
            prefer = getattr(self, "rdp_ucode", "f3d")
        bus = self.bus
        addr = u32(dl)
        for _ in range(64):
            w0 = bus.read_u32(addr)
            op = (w0 >> 24) & 0xFF
            if op in (0xBF, 0xB8, 0xBC, 0xBA, 0xB9):  # Fast3D markers
                return "f3d"
            if op in (0xDA, 0xDB, 0xDC, 0xDF, 0xD7, 0xD9):  # F3DEX2 markers
                return "f3dex2"
            if op == 0x05:  # G_TRI1 F3DEX2
                return "f3dex2"
            if op == 0x01:
                # Fast3D G_MTX has sizeof(Mtx)=0x40; F3DEX2 G_VTX uses other sizes.
                if (w0 & 0xFFFF) == 0x40:
                    return "f3d"
                return "f3dex2"
            if op == 0x06:
                if (w0 & 0x00FFFFFF) == 0:
                    return "f3d"  # gSPDisplayList
                return "f3dex2"  # G_TRI2
            if op == 0x04:
                return "f3d"  # G_VTX Fast3D
            addr = u32(addr + 8)
        return prefer

    def _hle_f3d_display_list(self, dl: int, max_bytes: int = 0x4000, _depth: int = 0, ucode: Optional[str] = None):
        """Fast3D / F3DEX2 walker: segments, matrices, VTX/TRI, fills, TEXRECT, nested DL."""
        if _depth > 24:
            return
        dl = u32(dl)
        if not dl:
            return
        if ucode is None:
            ucode = self._rdp_detect_ucode(dl)
            self.rdp_ucode = ucode
        bus = self.bus
        limit = dl + max(8, int(max_bytes))
        steps = 0
        f3dex2 = ucode == "f3dex2"
        while dl + 8 <= limit and steps < 8192:
            w0 = bus.read_u32(dl)
            w1 = bus.read_u32(dl + 4)
            op = (w0 >> 24) & 0xFF
            if op in (0xB8, 0xDF):  # G_ENDDL
                return
            elif op == 0xFF:  # G_SETCIMG
                self.rdp_color_width = ((w0 & 0xFFF) + 1) if (w0 & 0xFFF) else 320
                self.rdp_color_img = self._rdp_seg_addr(w1)
            elif op == 0xF7:  # G_SETFILLCOLOR
                self.rdp_fill_color = u32(w1)
            elif op == 0xF6:  # G_FILLRECT
                x1 = ((w0 >> 12) & 0xFFF) >> 2
                y1 = (w0 & 0xFFF) >> 2
                x0 = ((w1 >> 12) & 0xFFF) >> 2
                y0 = (w1 & 0xFFF) >> 2
                self._rdp_fill_rect(x0, y0, x1 + 1, y1 + 1)
            elif op == 0xE4:  # G_TEXRECT
                xh = ((w0 >> 12) & 0xFFF) >> 2
                yh = (w0 & 0xFFF) >> 2
                xl = ((w1 >> 12) & 0xFFF) >> 2
                yl = (w1 & 0xFFF) >> 2
                self._rdp_texrect(xl, yl, xh, yh)
                # Skip following RDPHALF ST/DSDX command if present.
                nxt = bus.read_u32(dl + 8)
                if ((nxt >> 24) & 0xFF) in (0xE1, 0xB4, 0xB3):
                    dl = u32(dl + 16)
                    steps += 1
                    continue
            elif op in (0xBC, 0xDB):  # G_MOVEWORD Fast3D / F3DEX2
                if f3dex2 or op == 0xDB:
                    index = (w0 >> 16) & 0xFF
                    offset = w0 & 0xFFFF
                else:
                    index = w0 & 0xFF
                    offset = (w0 >> 8) & 0xFFFF
                if index == 6:  # G_MW_SEGMENT
                    seg = (offset >> 2) & 0xF
                    self.rdp_segments[seg] = u32(w1) & 0x1FFFFFFF
            elif op == 0x03 and not f3dex2:  # G_MOVEMEM Fast3D viewport
                self._rdp_load_viewport(w1)
            elif op == 0xDC and f3dex2:  # G_MOVEMEM F3DEX2
                self._rdp_load_viewport(w1)
            elif op == 0x03 and f3dex2:
                pass  # G_CULLDL — skip
            elif op == 0x01 and not f3dex2:  # G_MTX Fast3D
                params = (w0 >> 16) & 0xFF
                self._rdp_apply_mtx(self._rdp_load_mtx(w1), params)
            elif op == 0xDA:  # G_MTX F3DEX2
                params = (w0 & 0xFF) ^ 0x01  # stored XOR G_MTX_PUSH
                self._rdp_apply_mtx(self._rdp_load_mtx(w1), params)
            elif op == 0x01 and f3dex2:  # G_VTX F3DEX2
                n = (w0 >> 12) & 0xFF
                vend = (w0 >> 1) & 0x7F
                v0 = max(0, vend - n)
                self._rdp_sp_vertex(w1, n, v0)
            elif op in (0xBD, 0xD8):  # G_POPMTX
                if self.rdp_mv_stack:
                    self.rdp_modelview = self.rdp_mv_stack.pop()
            elif op == 0x04 and not f3dex2:  # G_VTX Fast3D
                n = ((w0 >> 20) & 0xF) + 1
                v0 = ((w0 >> 16) & 0xF) >> 1
                self._rdp_sp_vertex(w1, n, v0)
            elif op == 0xBF or (op == 0x05 and f3dex2):  # G_TRI1
                v0 = ((w1 >> 16) & 0xFF) // 2
                v1 = ((w1 >> 8) & 0xFF) // 2
                v2 = (w1 & 0xFF) // 2
                self._rdp_draw_tri(v0, v1, v2)
            elif op == 0x06 and f3dex2:  # G_TRI2
                self._rdp_draw_tri(((w0 >> 16) & 0xFF) // 2, ((w0 >> 8) & 0xFF) // 2, (w0 & 0xFF) // 2)
                self._rdp_draw_tri(((w1 >> 16) & 0xFF) // 2, ((w1 >> 8) & 0xFF) // 2, (w1 & 0xFF) // 2)
            elif (op == 0x06 and not f3dex2) or op == 0xDE:  # G_DL
                branch = ((w0 >> 16) & 0xFF) != 0
                target = self._rdp_seg_addr(w1)
                if branch:
                    dl = target
                    steps += 1
                    continue
                self._hle_f3d_display_list(target, max_bytes=0x8000, _depth=_depth + 1, ucode=ucode)
            dl = u32(dl + 8)
            steps += 1

    def process_rdp(self):
        """HLE RDP: walk OSTask display list (fills + soft tris) and refresh VI framebuffer."""
        bus = self.bus
        bus.dpc_status &= ~DPC_STATUS_FREEZE
        start = bus.regs.get(DPC_START, 0)
        end = bus.regs.get(DPC_END, 0)
        bus.regs[DPC_CURRENT] = end
        # Fresh RSP-like transform state per graphics task.
        ident = self._rdp_mat_ident()
        self.rdp_modelview = [row[:] for row in ident]
        self.rdp_projection = [row[:] for row in ident]
        self.rdp_mv_stack = []
        self.rdp_vp_scale = [160.0, 120.0, 511.0, 0.0]
        self.rdp_vp_trans = [160.0, 120.0, 511.0, 0.0]
        self.rdp_ucode = "f3d"
        # Prefer OSTask data_ptr (F3D DL). Fall back to raw DPC span if present.
        task = u32(getattr(self, "last_os_task", 0))
        if task:
            data_ptr = bus.read_u32(task + 0x30)
            data_size = bus.read_u32(task + 0x34)
            if data_ptr:
                self._hle_f3d_display_list(data_ptr, max_bytes=max(0x200, data_size or 0x1000))
        elif end > start:
            self._hle_f3d_display_list(start | 0x80000000, max_bytes=max(8, end - start))
        bus.hw_interrupts |= MI_INTR_DP
        if bus.regs.get(VI_ORIGIN, 0):
            self.render_vi()
        elif self.rdp_color_img:
            phys = self.rdp_color_img & 0xFFFFFF
            if phys:
                bus.regs[VI_ORIGIN] = phys
                self._vi_origin_set = True
                self.render_vi()

    def process_audio(self):
        self.audio_signal = True
        self.bus.hw_interrupts |= MI_INTR_AI

    def boot_catch_up(self, max_s: float = 10.0, until_lit: bool = True) -> bool:
        """Burn interpreter time until VI presents (and optionally until lit title GFX).

        Used by the GUI worker so the canvas does not sit on ``VI=1,2,3…`` for minutes.
        """
        if not self.running:
            return False
        self.boot_turbo = True
        self.interp_steps = max(self.interp_steps, INTERP_BOOT_STEPS)
        t0 = time.perf_counter()
        while self.running and (time.perf_counter() - t0) < max_s:
            self.step_frame(budget_s=0.12)
            origin = self.bus.regs.get(VI_ORIGIN, 0) & 0xFFFFFF
            if until_lit and self.fb_lit:
                return True
            if (not until_lit) and origin and self.fb_ppm:
                return True
            # Once VI has an origin, keep going a bit for title GFX unless timed out.
            if origin and self.fb_ppm and (time.perf_counter() - t0) > 2.0 and not until_lit:
                return True
        return bool(self.fb_lit or (self.bus.regs.get(VI_ORIGIN, 0) & 0xFFFFFF))

    def render_vi(self, scale: int = 1):
        origin = self.bus.regs.get(VI_ORIGIN, 0) & 0xFFFFFF
        if origin == 0:
            return False
        width = self.bus.regs.get(VI_WIDTH, 320) & 0xFFF
        if width < 16 or width > 640:
            width = 320
        height = 240
        ppm = rdram_rgb5551_to_ppm(self.rdram, origin, width, height, scale=scale)
        if ppm is not None:
            self.fb_ppm = ppm
            if ppm_brightness(ppm) >= 8.0:
                self.fb_lit = True
                self.boot_turbo = False
            return True
        return False

    def step_frame(self, budget_s: float = INTERP_FRAME_BUDGET_S) -> int:
        """Run one displayed VI frame at N64 60/50 Hz semantics.

        Interprets as many instructions as fit in ``budget_s``, raises VI, advances
        COUNT toward a full N64 frame, and presents the framebuffer. Returns steps run.
        """
        if not self.running:
            return 0
        # CORN-style SM64-first: keep a high instruction budget until the first lit frame.
        if self.boot_turbo and not self.fb_lit:
            self.interp_steps = max(self.interp_steps, INTERP_BOOT_STEPS)
            budget_s = max(budget_s, 0.05)
        steps_target = max(INTERP_MIN_STEPS, min(INTERP_MAX_STEPS, int(self.interp_steps)))
        t0 = time.perf_counter()
        deadline = t0 + max(0.004, budget_s)
        ran = 0
        cpu = self.cpu
        spin_pc = cpu.pc & ~0x3F
        spin_hits = 0
        # Leave a little time for render_vi inside the same budget.
        cpu_deadline = t0 + max(0.003, budget_s * 0.85)
        while ran < steps_target and self.running:
            cpu.step()
            ran += 1
            pc = cpu.pc
            if (pc & ~0x3F) == spin_pc:
                spin_hits += 1
                if spin_hits >= 24:
                    # Accelerate software delay / decompress / poll loops.
                    cpu.cp0[CP0_COUNT] = u32(cpu.cp0[CP0_COUNT] + 2048)
                    spin_hits = 0
            else:
                spin_pc = pc & ~0x3F
                spin_hits = 0
            if (ran & 0xFF) == 0 and time.perf_counter() >= cpu_deadline:
                break
            # Preempt native spin loops when a higher-priority thread is ready
            # (e.g. after VI os_event woke the main thread while idle ran).
            if (ran & 0x1FF) == 0:
                self.ultrahle.maybe_preempt()
            # Fair share: rotate ready game threads so audio/main cannot starve gfx loader.
            if (ran & 0xFF) == 0:
                self.ultrahle.yield_fair()
        self.cycle_count += ran
        catch = max(0, self.cycles_per_frame - ran)
        if catch:
            prev = cpu.cp0[CP0_COUNT]
            cpu.cp0[CP0_COUNT] = u32(prev + catch)
            cmp_ = cpu.cp0[CP0_COMPARE]
            if cmp_ and u32(prev) < cmp_ <= cpu.cp0[CP0_COUNT]:
                cpu.cp0[CP0_CAUSE] |= CAUSE_IP7
        self.frame_count += 1
        vint = self.bus.regs.get(VI_INTR, 0x3FF) & 0x3FF
        self.bus.half_line = vint if vint else 0x200
        self.bus.hw_interrupts |= MI_INTR_VI
        # UltraHLE sync.c: inifile_patches(-1) every frame (e.g. Zelda language byte).
        if self.uh_sym.ini_patches:
            self.uh_sym.apply_ini_patches(-1)
        # UltraHLE sync.c fires RETRACE only. Firing VI+RETRACE doubles messages on
        # the same mq (SM64 audio kick + DMA share a size-1 queue) and drops DMA done.
        self.ultrahle.os_event(OS_EVENT_RETRACE)
        # VI may have woken the game thread — switch to it before the next frame.
        self.ultrahle.maybe_preempt()
        # If still on a low-pri idle/boot thread, force the best ready task.
        self.ultrahle.schedule(0)
        self.ultrahle.tick_time(self.cycles_per_frame)
        self.cheat_engine.apply(self.bus, self.rdram)
        # Present real VI framebuffer only — never inject a fake black PPM (that
        # left the GUI stuck on "waiting for VI framebuffer" forever).
        if time.perf_counter() < deadline or self.fb_ppm is None:
            self.render_vi(scale=1 if self.fb_lit else 2)
        elapsed = max(1e-6, time.perf_counter() - t0)
        # Aim next frame's CPU work at ~75% of the display period (or boot turbo).
        if self.boot_turbo and not self.fb_lit:
            self.interp_steps = INTERP_BOOT_STEPS
        else:
            target = max(0.004, (self.frame_period or FRAME_PERIOD_NTSC) * 0.75)
            rate = ran / elapsed
            self.interp_steps = int(max(INTERP_MIN_STEPS, min(INTERP_MAX_STEPS, rate * target)))
        return ran


# ── cathle classic Tkinter GUI ──
_COUNTRY_NAMES = {
    0x37: "Beta", 0x41: "NTSC", 0x44: "Germany", 0x45: "USA", 0x46: "France",
    0x49: "Italy", 0x4A: "Japan", 0x50: "Europe", 0x53: "Spain",
    0x55: "Australia", 0x58: "Europe", 0x59: "Europe",
}
_CIC_NAMES = {
    CIC_NUS_6101: "CIC-NUS-6101", CIC_NUS_6102: "CIC-NUS-6102",
    CIC_NUS_6103: "CIC-NUS-6103", CIC_NUS_6105: "CIC-NUS-6105",
    CIC_NUS_6106: "CIC-NUS-6106",
}


def _header_bytes_for_browser(raw):
    data = bytearray(raw[:0x40])
    if len(data) < 0x40:
        return data
    if data[:4] == V64_MAGIC:
        for i in range(0, len(data) - 1, 2):
            data[i], data[i + 1] = data[i + 1], data[i]
    elif data[:4] == N64_LE_MAGIC:
        for i in range(0, len(data) - 3, 4):
            data[i], data[i + 3] = data[i + 3], data[i]
            data[i + 1], data[i + 2] = data[i + 2], data[i + 1]
    return data


def _format_rom_size(size):
    mib = size / (1024 * 1024)
    return f"{mib:.1f} MB" if mib < 10 else f"{mib:.0f} MB"


class ROMBrowser(tk.Frame if tk else object):
    """Classic report-style ROM browser for cathle."""

    def __init__(self, parent, on_load, on_info, on_status, directory=None):
        if not tk:
            return
        super().__init__(parent, bg=CATHLE_WIN_GRAY, bd=0)
        self.on_load = on_load
        self.on_info = on_info
        self.on_status = on_status
        self.directory = directory or default_rom_directory()
        self.roms: List[Dict[str, Any]] = []
        self._items: Dict[str, Dict[str, Any]] = {}
        self._sort_column = "good_name"
        self._sort_reverse = False
        self.tree = None
        self.popup = None
        self._build_ui()
        self.scan_roms()

    def _build_ui(self):
        shell = tk.Frame(self, bg=CATHLE_WIN_GRAY, bd=1, relief=tk.SUNKEN)
        shell.pack(fill=tk.BOTH, expand=True, padx=2, pady=(1, 2))
        shell.rowconfigure(0, weight=1)
        shell.columnconfigure(0, weight=1)

        self.tree = ttk.Treeview(shell, columns=[c[0] for c in ROM_BROWSER_COLUMNS],
                                 show="headings", selectmode="browse")
        for key, title, width in ROM_BROWSER_COLUMNS:
            self.tree.heading(key, text=title, anchor=tk.W,
                              command=lambda column=key: self.sort_by(column))
            self.tree.column(key, width=width, minwidth=55, stretch=True, anchor=tk.W)
        self.tree.tag_configure("unknown", foreground="#666666")
        self.tree.tag_configure("compatible", foreground="#000000")
        self.tree.tag_configure("playable", foreground="#006600")
        self.tree.tag_configure("loaded", foreground="#006000")
        ybar = ttk.Scrollbar(shell, orient=tk.VERTICAL, command=self.tree.yview)
        xbar = ttk.Scrollbar(shell, orient=tk.HORIZONTAL, command=self.tree.xview)
        self.tree.configure(yscrollcommand=ybar.set, xscrollcommand=xbar.set)
        self.tree.grid(row=0, column=0, sticky="nsew")
        ybar.grid(row=0, column=1, sticky="ns")
        xbar.grid(row=1, column=0, sticky="ew")
        self.tree.bind("<Double-Button-1>", lambda _event: self._load_selected())
        self.tree.bind("<Return>", lambda _event: self._load_selected())
        self.tree.bind("<<TreeviewSelect>>", self._selection_changed)
        self.tree.bind("<Button-3>", self._show_popup)
        self.tree.bind("<Button-2>", self._show_popup)

        self.popup = tk.Menu(self, tearoff=False, font=UI_FONT)
        self.popup.add_command(label="Play Game", command=self._load_selected)
        self.popup.add_separator()
        self.popup.add_command(label="Refresh Rom List", command=self.scan_roms)
        self.popup.add_command(label="Choose Rom Directory...", command=self.choose_directory)
        self.popup.add_separator()
        self.popup.add_command(label="Rom Information", command=self._info_selected)
        self.popup.add_command(label="Game Information", command=self._info_selected)
        self.popup.add_separator()
        self.popup.add_command(label="Edit Game Settings", command=self._info_selected)
        self.popup.add_command(label="Edit Cheats", command=self._load_selected)

    def _read_entry(self, path):
        try:
            size = os.path.getsize(path)
            if size < 0x40:
                return None
            with open(path, "rb") as rom_file:
                raw = rom_file.read(0x1000)
        except OSError:
            return None
        header_data = _header_bytes_for_browser(raw)
        if len(header_data) < 0x40 or header_data[:4] != Z64_MAGIC:
            return None
        header = N64Header(header_data)
        title = header.title.strip() or os.path.splitext(os.path.basename(path))[0]
        country_code = header_data[0x3E]
        cic = get_cic_chip_id(header_data)
        known_cic = cic in (CIC_NUS_6101, CIC_NUS_6102, CIC_NUS_6103, CIC_NUS_6105, CIC_NUS_6106)
        status = "Playable" if known_cic else "Compatible"
        core_notes = "cathle+UltraHLE PATCH" if known_cic else "homebrew / unknown CIC"
        return {
            "path": path,
            "file_name": os.path.basename(path),
            "internal_name": header.title or "(unknown)",
            "good_name": title,
            "status": status,
            "core_notes": core_notes,
            "plugin_notes": "builtin VI/RDP/RSP HLE",
            "force_feedback": "No",
            "rom_size": _format_rom_size(size),
            "size": size,
            "header": header,
            "country": _COUNTRY_NAMES.get(country_code, f"0x{country_code:02X}"),
            "country_code": country_code,
            "cic": cic,
        }

    def scan_roms(self, directory=None):
        if directory:
            self.directory = directory
        self.roms.clear()
        self._items.clear()
        for item in self.tree.get_children():
            self.tree.delete(item)
        if not os.path.isdir(self.directory):
            self.on_status(f"Rom directory not found: {self.directory}")
            return
        self.on_status(f"Scanning {self.directory}...")
        found = 0
        try:
            for base, dirs, files in os.walk(self.directory):
                dirs[:] = [d for d in dirs if not d.startswith(".")]
                for name in sorted(files, key=str.casefold):
                    if not name.lower().endswith(ROM_EXTENSIONS):
                        continue
                    entry = self._read_entry(os.path.join(base, name))
                    if entry is None:
                        continue
                    self.roms.append(entry)
                    found += 1
                    if found >= _ROM_SCAN_MAX_FILES:
                        break
                if found >= _ROM_SCAN_MAX_FILES:
                    break
        except OSError as exc:
            self.on_status(f"Rom browser error: {exc}")
        self._populate()
        suffix = " (limit reached)" if found >= _ROM_SCAN_MAX_FILES else ""
        self.on_status(f"{found} Rom{'s' if found != 1 else ''} found{suffix}")

    def _populate(self):
        ordered = sorted(self.roms,
                         key=lambda row: str(row.get(self._sort_column, "")).casefold(),
                         reverse=self._sort_reverse)
        for entry in ordered:
            values = tuple(entry.get(key, "") for key, _title, _width in ROM_BROWSER_COLUMNS)
            tag = "playable" if entry.get("status") == "Playable" else (
                "compatible" if entry.get("status") == "Compatible" else "unknown")
            iid = self.tree.insert("", tk.END, values=values, tags=(tag,))
            self._items[iid] = entry

    def sort_by(self, column):
        if self._sort_column == column:
            self._sort_reverse = not self._sort_reverse
        else:
            self._sort_column = column
            self._sort_reverse = False
        for item in self.tree.get_children():
            self.tree.delete(item)
        self._items.clear()
        self._populate()

    def selected_entry(self):
        selection = self.tree.selection()
        return self._items.get(selection[0]) if selection else None

    def choose_directory(self):
        path = filedialog.askdirectory(initialdir=self.directory, title="Choose Rom Directory")
        if path:
            self.scan_roms(path)

    def mark_loaded(self, path):
        target = os.path.normcase(os.path.abspath(path))
        for iid, entry in self._items.items():
            if os.path.normcase(os.path.abspath(entry["path"])) == target:
                self.tree.selection_set(iid)
                self.tree.focus(iid)
                self.tree.see(iid)
                self.tree.item(iid, tags=("loaded",))
                return

    def _selection_changed(self, _event=None):
        entry = self.selected_entry()
        if entry:
            self.on_status(f"{entry['good_name']}  |  {entry['rom_size']}  |  {entry['country']}")

    def _load_selected(self):
        entry = self.selected_entry()
        if entry:
            self.on_load(entry["path"], True)

    def _info_selected(self):
        entry = self.selected_entry()
        if entry:
            self.on_info(entry)

    def _show_popup(self, event):
        row = self.tree.identify_row(event.y)
        if row:
            self.tree.selection_set(row)
            self.tree.focus(row)
            self.popup.tk_popup(event.x_root, event.y_root)


class CathleApp:
    def __init__(self):
        self.core = ACsN64Core()
        self.running = False
        self.loaded_path = ""
        self.recent_roms: List[str] = []
        self.state_slots: Dict[int, Dict[str, Any]] = {}
        self.current_slot = 0
        self._core_lock = threading.RLock()
        self._worker_stop = threading.Event()
        self._worker_wake = threading.Event()
        self._pending_error = ""
        self.emu_thread: Optional[threading.Thread] = None
        self.last_frame_count = 0
        self.fps_time = time.monotonic()
        self.limit_fps = True
        self.root = None
        if tk:
            self._build_gui()

    def _build_gui(self):
        self.root = tk.Tk()
        self.root.title(WINDOW_TITLE)
        self.root.geometry("900x570")
        self.root.minsize(640, 420)
        self.root.configure(bg=CATHLE_WIN_GRAY)
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

        style = ttk.Style(self.root)
        preferred = "winnative" if platform.system() == "Windows" else "classic"
        if preferred in style.theme_names():
            style.theme_use(preferred)
        style.configure("Treeview", background=CATHLE_PANEL_WHITE, foreground=CATHLE_TEXT,
                        fieldbackground=CATHLE_PANEL_WHITE, font=UI_FONT, rowheight=20,
                        borderwidth=0)
        style.configure("Treeview.Heading", font=UI_FONT_BOLD, relief=tk.RAISED)
        style.map("Treeview", background=[("selected", CATHLE_LIST_SEL_BG)],
                  foreground=[("selected", CATHLE_LIST_SEL_FG)])
        style.configure("TNotebook", background=CATHLE_WIN_GRAY)
        style.configure("TNotebook.Tab", font=UI_FONT, padding=(7, 3))

        self._install_embedded_icon()
        self.status_text = tk.StringVar(value="Ready")
        self.mode_text = tk.StringVar(value="Rom Browser")
        self.fps_text = tk.StringVar(value="")
        self.start_on_open_var = tk.BooleanVar(value=True)
        self.limit_fps_var = tk.BooleanVar(value=True)
        self.show_cpu_var = tk.BooleanVar(value=False)
        self.always_top_var = tk.BooleanVar(value=False)
        self.fullscreen_var = tk.BooleanVar(value=False)
        self.save_slot_var = tk.IntVar(value=0)
        self.rom_directory_var = tk.StringVar(value=default_rom_directory())
        self.menu_items: Dict[str, Tuple[Any, int]] = {}

        self._build_menus()
        self._build_toolbar()

        self.content = tk.Frame(self.root, bg=CATHLE_WIN_GRAY)
        self.content.pack(fill=tk.BOTH, expand=True)
        self.browser = ROMBrowser(self.content, self.load_rom, self.show_rom_info,
                                  self._set_status, self.rom_directory_var.get())
        self.browser.pack(fill=tk.BOTH, expand=True)

        self.emu_view = tk.Frame(self.content, bg="#000000", bd=2, relief=tk.SUNKEN)
        self.canvas = tk.Canvas(self.emu_view, bg="#000000", highlightthickness=0,
                                width=640, height=480)
        self.canvas.pack(fill=tk.BOTH, expand=True)
        self.canvas.bind("<Configure>", self._center_framebuffer)
        self.canvas_message = self.canvas.create_text(
            320, 220, text="cathle\nN64 emulator",
            fill="#b0b0b0", justify=tk.CENTER, font=("Tahoma", 15, "bold"),
            tags=("splash",)
        )
        self._canvas_prompt = "splash"

        self._build_status_bar()
        self._bind_shortcuts()
        self._update_actions()
        self.root.after(16, self._poll)
        self.emu_thread = threading.Thread(target=self._emulation_worker,
                                           name="cathle-r4300i", daemon=True)
        self.emu_thread.start()

    def _install_embedded_icon(self):
        icon = tk.PhotoImage(width=16, height=16)
        icon.put("#202020", to=(1, 1, 15, 15))
        icon.put("#dd2020", to=(2, 2, 8, 8))
        icon.put("#22a044", to=(8, 2, 14, 8))
        icon.put("#2560d8", to=(2, 8, 8, 14))
        icon.put("#e7c51e", to=(8, 8, 14, 14))
        icon.put("#ffffff", to=(6, 4, 10, 12))
        self._app_icon = icon
        try:
            self.root.iconphoto(True, icon)
        except tk.TclError:
            pass

    def _add_menu_command(self, menu, key, label, command, accelerator="", state=tk.NORMAL):
        menu.add_command(label=label, command=command, accelerator=accelerator,
                         state=state, font=UI_FONT)
        self.menu_items[key] = (menu, menu.index(tk.END))

    def _build_menus(self):
        menubar = tk.Menu(self.root, tearoff=False, font=UI_FONT)
        self.root.configure(menu=menubar)

        file_menu = tk.Menu(menubar, tearoff=False, font=UI_FONT)
        menubar.add_cascade(label="File", menu=file_menu)
        self._add_menu_command(file_menu, "open", "Open Rom...", self.open_rom_dialog, "Ctrl+O")
        self._add_menu_command(file_menu, "rom_info", "Rom Information", self.show_loaded_rom_info,
                               "Ctrl+I", tk.DISABLED)
        self._add_menu_command(file_menu, "game_info", "Game Information", self.show_loaded_rom_info,
                               "Ctrl+G", tk.DISABLED)
        file_menu.add_separator()
        self._add_menu_command(file_menu, "start", "Start Emulation", self.start_emulation,
                               "F10", tk.DISABLED)
        self._add_menu_command(file_menu, "end", "End Emulation", self.end_emulation,
                               "F11", tk.DISABLED)
        file_menu.add_separator()
        language_menu = tk.Menu(file_menu, tearoff=False, font=UI_FONT)
        language_menu.add_command(label="English", state=tk.DISABLED)
        file_menu.add_cascade(label="Language", menu=language_menu)
        file_menu.add_separator()
        self._add_menu_command(file_menu, "choose_dir", "Choose Rom Directory...",
                               self.choose_rom_directory)
        self._add_menu_command(file_menu, "refresh", "Refresh Rom List",
                               lambda: self.browser.scan_roms(), "F5")
        file_menu.add_separator()
        self.recent_menu = tk.Menu(file_menu, tearoff=False, font=UI_FONT)
        self.recent_menu.add_command(label="None Here", state=tk.DISABLED)
        file_menu.add_cascade(label="Recent Rom", menu=self.recent_menu)
        self.recent_dir_menu = tk.Menu(file_menu, tearoff=False, font=UI_FONT)
        self.recent_dir_menu.add_command(label="None Here", state=tk.DISABLED)
        file_menu.add_cascade(label="Recent Rom Directories", menu=self.recent_dir_menu)
        file_menu.add_separator()
        self._add_menu_command(file_menu, "exit", "Exit", self._on_close)

        system_menu = tk.Menu(menubar, tearoff=False, font=UI_FONT)
        menubar.add_cascade(label="System", menu=system_menu)
        self._add_menu_command(system_menu, "reset", "Reset", self.reset_core, "F1", tk.DISABLED)
        self._add_menu_command(system_menu, "pause", "Pause", self.pause_emulation, "F2", tk.DISABLED)
        self._add_menu_command(system_menu, "screenshot", "Screenshot Capture",
                               self.capture_screenshot, "F3", tk.DISABLED)
        system_menu.add_separator()
        system_menu.add_checkbutton(label="Limit FPS", variable=self.limit_fps_var,
                                    accelerator="F4", command=self._sync_options, font=UI_FONT)
        system_menu.add_separator()
        self._add_menu_command(system_menu, "save", "Save", self.save_state, "F5", tk.DISABLED)
        self._add_menu_command(system_menu, "save_as", "Save As...", self.save_state,
                               "Ctrl+S", tk.DISABLED)
        self._add_menu_command(system_menu, "restore", "Restore", self.restore_state,
                               "F7", tk.DISABLED)
        self._add_menu_command(system_menu, "restore_from", "Restore From", self.restore_state,
                               "Ctrl+L", tk.DISABLED)
        system_menu.add_separator()
        slot_menu = tk.Menu(system_menu, tearoff=False, font=UI_FONT)
        slot_menu.add_radiobutton(label="Default", value=0, variable=self.save_slot_var,
                                  command=self._slot_changed, accelerator="0")
        slot_menu.add_separator()
        for slot in range(1, 10):
            slot_menu.add_radiobutton(label=f"Slot {slot}", value=slot,
                                      variable=self.save_slot_var, command=self._slot_changed,
                                      accelerator=str(slot))
        system_menu.add_cascade(label="Current Save State", menu=slot_menu)
        system_menu.add_separator()
        self._add_menu_command(system_menu, "cheats", "Cheats...", self.show_cheats,
                               "Ctrl+C", tk.DISABLED)
        self._add_menu_command(system_menu, "cheat_search", "Cheat Search",
                               self.show_cheats, "Ctrl+R", tk.DISABLED)
        self._add_menu_command(system_menu, "gs_button", "GS Button",
                               lambda: self._set_status("GS Button pressed"), "F9", tk.DISABLED)

        options_menu = tk.Menu(menubar, tearoff=False, font=UI_FONT)
        menubar.add_cascade(label="Options", menu=options_menu)
        options_menu.add_checkbutton(label="Full Screen", variable=self.fullscreen_var,
                                     command=self.toggle_fullscreen, accelerator="Alt+Enter",
                                     font=UI_FONT)
        options_menu.add_checkbutton(label="Always On Top", variable=self.always_top_var,
                                     command=self.toggle_always_on_top, accelerator="Ctrl+A",
                                     font=UI_FONT)
        options_menu.add_separator()
        self._add_menu_command(options_menu, "gfx_plugin", "Configure Graphics Plugin...",
                               lambda: self.show_settings("Plugins"), "Ctrl+V")
        self._add_menu_command(options_menu, "audio_plugin", "Configure Audio Plugin...",
                               lambda: self.show_settings("Plugins"), "Ctrl+U")
        self._add_menu_command(options_menu, "control_plugin", "Configure Controller Plugin...",
                               lambda: self.show_settings("Plugins"), "Ctrl+X")
        self._add_menu_command(options_menu, "rsp_plugin", "Configure RSP Plugin...",
                               lambda: self.show_settings("Plugins"), "Ctrl+W")
        options_menu.add_separator()
        options_menu.add_checkbutton(label="Show CPU usage %", variable=self.show_cpu_var,
                                     font=UI_FONT)
        self._add_menu_command(options_menu, "settings", "Settings...",
                               self.show_settings, "Ctrl+T")

        debugger_menu = tk.Menu(menubar, tearoff=False, font=UI_FONT)
        menubar.add_cascade(label="Debugger", menu=debugger_menu)
        self._add_menu_command(debugger_menu, "breakpoint", "Set Breakpoint...",
                               self.set_breakpoint, state=tk.DISABLED)
        debugger_menu.add_separator()
        r4300_menu = tk.Menu(debugger_menu, tearoff=False, font=UI_FONT)
        r4300_menu.add_command(label="R4300i Commands...", command=self.show_registers)
        r4300_menu.add_command(label="R4300i Registers...", command=self.show_registers)
        debugger_menu.add_cascade(label="R4300i", menu=r4300_menu)
        self._add_menu_command(debugger_menu, "memory", "Memory...", self.show_memory,
                               state=tk.DISABLED)
        self._add_menu_command(debugger_menu, "tlb", "TLB Entries...", self.show_tlb,
                               state=tk.DISABLED)
        debugger_menu.add_separator()
        debugger_menu.add_command(label="Call Stack...", state=tk.DISABLED, font=UI_FONT)
        debugger_menu.add_separator()
        logging_menu = tk.Menu(debugger_menu, tearoff=False, font=UI_FONT)
        logging_menu.add_command(label="Log Options", command=lambda: self._set_status("Logging options"))
        logging_menu.add_command(label="Generate Log", command=lambda: self._set_status("Log generated"))
        debugger_menu.add_cascade(label="Logging", menu=logging_menu)

        help_menu = tk.Menu(menubar, tearoff=False, font=UI_FONT)
        menubar.add_cascade(label="Help", menu=help_menu)
        help_menu.add_command(label="Quick Start...", command=lambda: messagebox.showinfo(
            "cathle Quick Start",
            "1. Choose File > Open Rom.\n"
            "2. Select a .z64, .v64, or .n64 image.\n"
            "3. Use System to pause, reset, save, or restore.\n"
            "4. Press Alt+Enter to toggle full screen."
        ), font=UI_FONT)
        help_menu.add_command(label="Keyboard Shortcuts...", command=lambda: messagebox.showinfo(
            "cathle Keyboard Shortcuts",
            "Ctrl+O  Open Rom\n"
            "F1  Reset\nF2  Pause\nF3  Screenshot\n"
            "F5  Refresh or save state\nF7  Restore state\n"
            "F10  Start\nF11  End\nAlt+Enter  Full screen"
        ), font=UI_FONT)
        help_menu.add_separator()
        help_menu.add_command(label="About INI Files", command=lambda: messagebox.showinfo(
            "About settings", "cathle keeps this edition self-contained; no INI files are required."),
                              font=UI_FONT)
        help_menu.add_command(label="About cathle", command=self.show_about, font=UI_FONT)

    def _build_toolbar(self):
        self.toolbar = tk.Frame(self.root, bg=CATHLE_WIN_GRAY, bd=1, relief=tk.RAISED)
        self.toolbar.pack(fill=tk.X)
        self.toolbar_buttons: Dict[str, tk.Button] = {}

        def add_button(key, text, command, width=7):
            button = tk.Button(self.toolbar, text=text, font=UI_FONT, command=command,
                               width=width, padx=2, pady=1, relief=tk.RAISED,
                               bd=1, takefocus=False, bg=CATHLE_BTN_FACE,
                               activebackground=CATHLE_BTN_HIGHLIGHT)
            button.pack(side=tk.LEFT, padx=(2, 0), pady=2)
            self.toolbar_buttons[key] = button

        def separator():
            tk.Frame(self.toolbar, width=2, bg=CATHLE_BTN_SHADOW,
                     bd=1, relief=tk.SUNKEN).pack(side=tk.LEFT, fill=tk.Y, padx=4, pady=3)

        add_button("open", "Open", self.open_rom_dialog)
        add_button("browser", "Roms", self.show_browser)
        separator()
        add_button("start", "Start", self.start_emulation)
        add_button("pause", "Pause", self.pause_emulation)
        add_button("reset", "Reset", self.reset_core)
        add_button("end", "End", self.end_emulation)
        separator()
        add_button("screenshot", "Capture", self.capture_screenshot, 8)
        add_button("settings", "Settings", self.show_settings, 8)

    def _build_status_bar(self):
        bar = tk.Frame(self.root, bg=CATHLE_WIN_GRAY, bd=1, relief=tk.RAISED)
        bar.pack(fill=tk.X, side=tk.BOTTOM)
        tk.Label(bar, textvariable=self.status_text, font=UI_FONT, bg=CATHLE_WIN_GRAY,
                 fg=CATHLE_TEXT, anchor=tk.W, relief=tk.SUNKEN, bd=1
                 ).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(1, 0), pady=1)
        tk.Label(bar, textvariable=self.mode_text, font=UI_FONT, bg=CATHLE_WIN_GRAY,
                 fg=CATHLE_TEXT, anchor=tk.CENTER, relief=tk.SUNKEN, bd=1, width=16
                 ).pack(side=tk.LEFT, padx=(2, 0), pady=1)
        tk.Label(bar, textvariable=self.fps_text, font=UI_FONT_MONO, bg=CATHLE_WIN_GRAY,
                 fg=CATHLE_TEXT, anchor=tk.CENTER, relief=tk.SUNKEN, bd=1, width=10
                 ).pack(side=tk.LEFT, padx=(2, 1), pady=1)

    def _bind_shortcuts(self):
        bindings = {
            "<Control-o>": self.open_rom_dialog, "<Control-i>": self.show_loaded_rom_info,
            "<Control-g>": self.show_loaded_rom_info, "<F10>": self.start_emulation,
            "<F11>": self.end_emulation, "<F1>": self.reset_core,
            "<F2>": self.pause_emulation, "<Pause>": self.pause_emulation,
            "<F3>": self.capture_screenshot, "<F4>": self._toggle_limit,
            "<F5>": self._f5_action, "<F7>": self.restore_state,
            "<F9>": lambda: self._set_status("GS Button pressed"),
            "<Control-s>": self.save_state, "<Control-l>": self.restore_state,
            "<Control-c>": self.show_cheats, "<Control-r>": self.show_cheats,
            "<Control-a>": self._toggle_top, "<Control-t>": self.show_settings,
            "<Alt-Return>": self._toggle_fullscreen_key,
        }
        for sequence, callback in bindings.items():
            self.root.bind_all(sequence, lambda event, fn=callback: self._shortcut(fn))
        for slot in range(10):
            self.root.bind_all(str(slot), lambda event, value=slot: self._choose_slot(value))

    def _shortcut(self, callback):
        callback()
        return "break"

    def _set_status(self, text):
        if self.status_text is not None:
            self.status_text.set(text)

    def _set_item_state(self, key, enabled):
        item = self.menu_items.get(key)
        if item:
            item[0].entryconfigure(item[1], state=tk.NORMAL if enabled else tk.DISABLED)

    def _update_actions(self):
        loaded = bool(self.core.rom and self.loaded_path)
        for key in ("rom_info", "game_info", "start", "end", "reset", "pause",
                    "screenshot", "save", "save_as", "restore", "restore_from",
                    "cheats", "cheat_search", "gs_button", "breakpoint", "memory", "tlb"):
            self._set_item_state(key, loaded)
        for key in ("start", "pause", "reset", "end", "screenshot"):
            if key in self.toolbar_buttons:
                self.toolbar_buttons[key].configure(state=tk.NORMAL if loaded else tk.DISABLED)
        if "start" in self.toolbar_buttons:
            self.toolbar_buttons["start"].configure(state=tk.DISABLED if self.running or not loaded else tk.NORMAL)
        if "pause" in self.toolbar_buttons:
            self.toolbar_buttons["pause"].configure(state=tk.NORMAL if self.running else tk.DISABLED)
        self._set_item_state("start", loaded and not self.running)
        self._set_item_state("pause", loaded and self.running)

    def _sync_options(self):
        self.limit_fps = bool(self.limit_fps_var.get())
        self._set_status("Speed limiter on" if self.limit_fps else "Speed limiter off")

    def _toggle_limit(self):
        self.limit_fps_var.set(not self.limit_fps_var.get())
        self._sync_options()

    def _f5_action(self):
        if self.running:
            self.save_state()
        else:
            self.browser.scan_roms()

    def _toggle_top(self):
        self.always_top_var.set(not self.always_top_var.get())
        self.toggle_always_on_top()

    def _toggle_fullscreen_key(self):
        self.fullscreen_var.set(not self.fullscreen_var.get())
        self.toggle_fullscreen()

    def _choose_slot(self, slot):
        self.save_slot_var.set(slot)
        self._slot_changed()

    def _slot_changed(self):
        self.current_slot = int(self.save_slot_var.get())
        name = "Default" if self.current_slot == 0 else f"Slot {self.current_slot}"
        self._set_status(f"Current save state: {name}")

    def open_rom_dialog(self):
        path = filedialog.askopenfilename(
            title="Open Rom",
            initialdir=self.rom_directory_var.get(),
            filetypes=[("N64 Rom images", "*.z64 *.v64 *.n64 *.rom *.bin"),
                       ("All files", "*.*")]
        )
        if path:
            self.load_rom(path, bool(self.start_on_open_var.get()))

    def choose_rom_directory(self):
        path = filedialog.askdirectory(initialdir=self.rom_directory_var.get(),
                                       title="Choose Rom Directory")
        if path:
            self.rom_directory_var.set(path)
            self.browser.scan_roms(path)
            self._update_recent_directories(path)

    def _update_recent_directories(self, path):
        self.recent_dir_menu.delete(0, tk.END)
        self.recent_dir_menu.add_command(label=path,
                                         command=lambda p=path: self.browser.scan_roms(p))

    def _remember_rom(self, path):
        path = os.path.abspath(path)
        self.recent_roms = [item for item in self.recent_roms
                            if os.path.normcase(item) != os.path.normcase(path)]
        self.recent_roms.insert(0, path)
        del self.recent_roms[10:]
        self.recent_menu.delete(0, tk.END)
        for index, item in enumerate(self.recent_roms, 1):
            self.recent_menu.add_command(
                label=f"{index}. {os.path.basename(item)}",
                command=lambda rom=item: self.load_rom(rom, bool(self.start_on_open_var.get()))
            )

    def load_rom(self, path, auto_start=True):
        self.running = False
        self.core.running = False
        with self._core_lock:
            err = self.core.load_rom(path)
        if err:
            messagebox.showerror("Load Error", err)
            self._set_status(f"Error: {err}")
            return
        self.loaded_path = os.path.abspath(path)
        # Target true N64 VI rate; step_frame adapts instruction count to hold 60/50 Hz.
        self.core.cycle_limit = INTERP_MAX_STEPS
        self.browser.mark_loaded(path)
        self._remember_rom(path)
        self._update_recent_directories(os.path.dirname(self.loaded_path))
        title = self.core.rom_header.title if self.core.rom_header else os.path.basename(path)
        self.root.title(f"{title} - {WINDOW_TITLE}")
        self._set_status(f"Loaded: {os.path.basename(path)}")
        self.mode_text.set("Loaded")
        self.show_emulation()
        if auto_start:
            self.start_emulation()
        else:
            self._update_actions()

    def start_emulation(self):
        if not self.core.rom or not self.loaded_path:
            self.open_rom_dialog()
            return
        self.show_emulation()
        self.running = True
        self.core.running = True
        self.core.boot_turbo = True
        self.core.fb_lit = False
        self.core.interp_steps = INTERP_BOOT_STEPS
        self._boot_catchup_done = False
        self._display_ppm = None
        self._display_lit = False
        self._display_origin = 0
        self._display_frame = 0
        self._last_blit_bytes = None
        try:
            self.canvas.image = None
            self.canvas.delete("framebuffer")
        except Exception:
            pass
        self._worker_wake.set()
        self.mode_text.set("Booting")
        self._set_status("Booting…")
        self._set_canvas_prompt("booting", "Booting…")
        self._update_actions()

    def pause_emulation(self):
        if not self.core.rom:
            return
        self.running = False
        self.core.running = False
        self.mode_text.set("Paused")
        self._set_status("Emulation paused")
        self._set_canvas_prompt("paused")
        self._update_actions()

    def toggle_emu(self):
        self.pause_emulation() if self.running else self.start_emulation()

    def end_emulation(self):
        if not self.core.rom:
            return
        self.running = False
        self.core.running = False
        self.mode_text.set("Rom Browser")
        self.fps_text.set("")
        self._set_status("Emulation ended")
        try:
            self.canvas.delete("framebuffer")
            self.canvas.image = None
        except (tk.TclError, AttributeError):
            pass
        self.core.fb_ppm = None
        self._set_canvas_prompt("splash")
        self.show_browser()
        self._update_actions()

    def reset_core(self):
        if not self.core.rom:
            return
        was_running = self.running
        self.running = False
        self.core.running = False
        with self._core_lock:
            # Full IPL3 HLE reboot — plain reset() wiped RDRAM and left PC on empty RAM.
            self.core.reset()
            self.core._hle_ipl3_boot()
            self.core.fb_ppm = None
            self.core.fb_lit = False
            self.core.boot_turbo = True
            self.core.interp_steps = INTERP_BOOT_STEPS
            self._boot_catchup_done = False
            self._last_blit_ppm = None
        try:
            self.canvas.delete("framebuffer")
            self.canvas.image = None
        except (tk.TclError, AttributeError):
            pass
        self.running = was_running
        self.core.running = was_running
        if was_running:
            self._worker_wake.set()
            self._set_canvas_prompt("booting")
        self._set_status("System reset")
        self.mode_text.set("Running" if was_running else "Paused")
        self._update_actions()

    def show_browser(self):
        self.emu_view.pack_forget()
        if not self.browser.winfo_ismapped():
            self.browser.pack(fill=tk.BOTH, expand=True)
        if not self.running:
            self.mode_text.set("Rom Browser")

    def show_emulation(self):
        self.browser.pack_forget()
        if not self.emu_view.winfo_ismapped():
            self.emu_view.pack(fill=tk.BOTH, expand=True)
        self._set_canvas_prompt("booting" if self.running or self.core.rom else "splash")

    def _set_canvas_prompt(self, mode: str, detail: str = ""):
        """Idle splash vs boot caption. Hidden once a framebuffer image is on screen."""
        if not self.canvas:
            return
        if getattr(self.canvas, "image", None) is not None and mode != "splash":
            return
        if mode == "booting":
            text = detail or "Booting…\nstarting VI"
        elif mode == "paused":
            text = "Paused"
        else:
            text = "cathle\nN64 emulator"
        try:
            self.canvas.delete("splash")
            width = max(320, self.canvas.winfo_width())
            height = max(240, self.canvas.winfo_height())
            self.canvas_message = self.canvas.create_text(
                width // 2, height // 2, text=text,
                fill="#b0b0b0", justify=tk.CENTER, font=("Tahoma", 15, "bold"),
                tags=("splash",)
            )
            self._canvas_prompt = mode
            self._canvas_prompt_detail = detail
        except tk.TclError:
            pass

    def _emulation_worker(self):
        """Drive the core at N64 VI rate (60 Hz NTSC / 50 Hz PAL)."""
        next_frame = time.perf_counter()
        while not self._worker_stop.is_set():
            if not self.running:
                self._worker_wake.wait(0.05)
                self._worker_wake.clear()
                next_frame = time.perf_counter()
                continue
            period = self.core.frame_period or FRAME_PERIOD_NTSC
            frame_start = time.perf_counter()
            try:
                boot = self.core.boot_turbo and not self.core.fb_lit
                slices = 12 if boot else 1
                for _ in range(slices):
                    if not self.running or self._worker_stop.is_set():
                        break
                    with self._core_lock:
                        self.core.running = self.running
                        if self.core.boot_turbo and not self.core.fb_lit:
                            budget = 0.12
                        elif self.limit_fps:
                            budget = max(0.008, period - 0.003)
                        else:
                            budget = min(0.05, period * 2)
                        self.core.step_frame(budget_s=budget)
                        # Publish a lock-free present snapshot for the UI thread.
                        origin = self.core.bus.regs.get(VI_ORIGIN, 0) & 0xFFFFFF
                        if origin and self.core.fb_ppm is None:
                            self.core.render_vi(scale=1)
                        if origin and self.core.fb_ppm:
                            self._display_ppm = bytes(self.core.fb_ppm)
                            self._display_origin = origin
                            self._display_lit = bool(self.core.fb_lit)
                            self._display_frame = self.core.frame_count
                    if self.core.fb_lit:
                        break
            except Exception as exc:
                self._pending_error = f"{type(exc).__name__}: {exc}"
                self.running = False
                self.core.running = False
            if self.limit_fps and self.core.fb_lit:
                next_frame += period
                now = time.perf_counter()
                if now > next_frame + period * 2:
                    next_frame = now
                delay = next_frame - now
                if delay > 0.0004:
                    self._worker_stop.wait(delay)
                elif delay < -period:
                    next_frame = now
            else:
                if time.perf_counter() - frame_start < 0.0005:
                    self._worker_stop.wait(0.0)

    def _poll(self):
        if not self.root:
            return
        if self._pending_error:
            error = self._pending_error
            self._pending_error = ""
            self.mode_text.set("Stopped")
            self._set_status(f"Core stopped: {error}")
            messagebox.showerror("Emulation Error", error)
            self._update_actions()
        if self.emu_view.winfo_ismapped():
            self._blit_framebuffer()
        now = time.monotonic()
        if now - self.fps_time >= 1.0:
            frames = self.core.frame_count - self.last_frame_count
            self.last_frame_count = self.core.frame_count
            self.fps_time = now
            if self.running:
                cpu = f" | {min(100, max(0, frames * 100 // 60))}% CPU" if self.show_cpu_var.get() else ""
                target = 60 if abs((self.core.frame_period or FRAME_PERIOD_NTSC) - FRAME_PERIOD_NTSC) < 0.001 else 50
                self.fps_text.set(f"{frames}/{target} VI/s{cpu}")
            else:
                self.fps_text.set("")
        self.root.after(16, self._poll)

    def _blit_framebuffer(self):
        """Blit the worker's lock-free display snapshot (no core lock on UI thread)."""
        ppm = getattr(self, "_display_ppm", None)
        origin = getattr(self, "_display_origin", 0)
        lit = getattr(self, "_display_lit", False)
        frame_n = getattr(self, "_display_frame", 0) or self.core.frame_count
        if not ppm or not origin:
            if self.running and not getattr(self.canvas, "image", None):
                now = time.monotonic()
                last = getattr(self, "_boot_prompt_t", 0.0)
                if now - last >= 0.5:
                    self._boot_prompt_t = now
                    self._set_canvas_prompt("booting", "Booting…")
                    self._set_status(f"Booting… ({frame_n})")
            return
        if getattr(self, "_last_blit_bytes", None) == ppm and getattr(self.canvas, "image", None) is not None:
            return
        image = None
        try:
            import tempfile
            path = getattr(self, "_fb_ppm_path", None)
            if not path:
                fd, path = tempfile.mkstemp(suffix=".ppm", prefix="cathle_fb_", dir="/tmp")
                os.close(fd)
                self._fb_ppm_path = path
            with open(path, "wb") as f:
                f.write(ppm)
            image = tk.PhotoImage(file=path)
            try:
                if image.width() <= 200:
                    image = image.zoom(2, 2)
            except tk.TclError:
                pass
        except Exception:
            try:
                b64 = base64.b64encode(ppm).decode("ascii")
                image = tk.PhotoImage(data=b64)
                try:
                    if image.width() <= 200:
                        image = image.zoom(2, 2)
                except tk.TclError:
                    pass
            except Exception as exc:
                self._set_status(f"Present failed: {exc}")
                image = None
        if image is None:
            return
        try:
            self.canvas.delete("framebuffer")
            self.canvas.delete("splash")
            x = max(0, self.canvas.winfo_width() // 2)
            y = max(0, self.canvas.winfo_height() // 2)
            self.canvas.create_image(x, y, anchor=tk.CENTER, image=image, tags=("framebuffer",))
            self.canvas.image = image
            self._last_blit_bytes = ppm
            self._canvas_prompt = "frame"
            if self.running:
                if lit:
                    self.mode_text.set("Running")
                    self._set_status("Running")
                else:
                    self.mode_text.set("Booting")
                    self._set_status(f"VI @ {origin:06X}")
        except tk.TclError:
            pass

    def _center_framebuffer(self, _event=None):
        if getattr(self.canvas, "image", None) is not None:
            try:
                x = max(0, self.canvas.winfo_width() // 2)
                y = max(0, self.canvas.winfo_height() // 2)
                self.canvas.coords("framebuffer", x, y)
            except tk.TclError:
                pass
            return
        width = max(1, self.canvas.winfo_width())
        height = max(1, self.canvas.winfo_height())
        try:
            self.canvas.coords(self.canvas_message, width // 2, height // 2)
        except tk.TclError:
            pass

    def _capture_state(self):
        cpu = self.core.cpu
        bus = self.core.bus
        return {
            "rdram": bytes(self.core.rdram),
            "rsp_dmem": bytes(self.core.rsp_dmem),
            "rsp_imem": bytes(self.core.rsp_imem),
            "pif_ram": bytes(self.core.pif_ram),
            "gpr": list(cpu.gpr), "fpr": list(cpu.fpr), "cp0": list(cpu.cp0),
            "fcr31": cpu.fcr31, "hi": cpu.hi, "lo": cpu.lo,
            "pc": cpu.pc, "next_pc": cpu.next_pc,
            "llbit": cpu.llbit, "lladdr": cpu.lladdr,
            "regs": dict(bus.regs), "hw_interrupts": bus.hw_interrupts,
            "mi_intr_mask": bus.mi_intr_mask, "mi_mode": bus.mi_mode,
            "sp_status": bus.sp_status, "dpc_status": bus.dpc_status,
            "frame_count": self.core.frame_count, "cycle_count": self.core.cycle_count,
            "rom_path": self.loaded_path,
        }

    def save_state(self):
        if not self.core.rom:
            return
        with self._core_lock:
            self.state_slots[self.current_slot] = self._capture_state()
        name = "Default" if self.current_slot == 0 else f"Slot {self.current_slot}"
        self._set_status(f"State saved to {name} (memory)")

    def restore_state(self):
        if not self.core.rom:
            return
        state = self.state_slots.get(self.current_slot)
        if state is None:
            name = "Default" if self.current_slot == 0 else f"Slot {self.current_slot}"
            self._set_status(f"No state stored in {name}")
            return
        if os.path.normcase(state["rom_path"]) != os.path.normcase(self.loaded_path):
            messagebox.showwarning("Restore State", "This state belongs to another Rom.")
            return
        with self._core_lock:
            self.core.rdram[:] = state["rdram"]
            self.core.rsp_dmem[:] = state["rsp_dmem"]
            self.core.rsp_imem[:] = state["rsp_imem"]
            self.core.pif_ram[:] = state["pif_ram"]
            cpu = self.core.cpu
            cpu.gpr[:] = state["gpr"]; cpu.fpr[:] = state["fpr"]; cpu.cp0[:] = state["cp0"]
            cpu.fcr31 = state["fcr31"]; cpu.hi = state["hi"]; cpu.lo = state["lo"]
            cpu.pc = state["pc"]; cpu.next_pc = state["next_pc"]
            cpu.llbit = state["llbit"]; cpu.lladdr = state["lladdr"]
            bus = self.core.bus
            bus.regs = dict(state["regs"]); bus.hw_interrupts = state["hw_interrupts"]
            bus.mi_intr_mask = state["mi_intr_mask"]; bus.mi_mode = state["mi_mode"]
            bus.sp_status = state["sp_status"]; bus.dpc_status = state["dpc_status"]
            self.core.frame_count = state["frame_count"]
            self.core.cycle_count = state["cycle_count"]
        name = "Default" if self.current_slot == 0 else f"Slot {self.current_slot}"
        self._set_status(f"State restored from {name}")

    def capture_screenshot(self):
        if not self.core.fb_ppm:
            self._set_status("No framebuffer is available yet")
            return
        path = filedialog.asksaveasfilename(
            title="Screenshot Capture", defaultextension=".ppm",
            initialfile=f"{os.path.splitext(os.path.basename(self.loaded_path))[0]}-capture.ppm",
            filetypes=[("Portable Pixmap", "*.ppm"), ("All files", "*.*")]
        )
        if path:
            try:
                with open(path, "wb") as image_file:
                    image_file.write(self.core.fb_ppm)
                self._set_status(f"Screenshot saved: {os.path.basename(path)}")
            except OSError as exc:
                messagebox.showerror("Screenshot Capture", str(exc))

    def toggle_fullscreen(self):
        try:
            self.root.attributes("-fullscreen", bool(self.fullscreen_var.get()))
        except tk.TclError:
            pass

    def toggle_always_on_top(self):
        try:
            self.root.attributes("-topmost", bool(self.always_top_var.get()))
        except tk.TclError:
            pass

    def _browser_entry_for_loaded(self):
        target = os.path.normcase(os.path.abspath(self.loaded_path)) if self.loaded_path else ""
        for entry in self.browser.roms:
            if os.path.normcase(os.path.abspath(entry["path"])) == target:
                return entry
        if self.core.rom_header and self.loaded_path:
            header = self.core.rom_header
            return {
                "path": self.loaded_path, "file_name": os.path.basename(self.loaded_path),
                "good_name": header.title or os.path.basename(self.loaded_path),
                "internal_name": header.title or "(unknown)", "header": header,
                "size": len(self.core.rom), "rom_size": _format_rom_size(len(self.core.rom)),
                "country_code": self.core.rom[0x3E] if len(self.core.rom) > 0x3E else 0,
                "country": _COUNTRY_NAMES.get(self.core.rom[0x3E], "Unknown") if len(self.core.rom) > 0x3E else "Unknown",
                "cic": self.core.cic,
            }
        return None

    def show_loaded_rom_info(self):
        entry = self._browser_entry_for_loaded()
        if entry:
            self.show_rom_info(entry)

    def show_rom_info(self, entry):
        header = entry["header"]
        dialog = tk.Toplevel(self.root)
        dialog.title("Rom Information")
        dialog.configure(bg=CATHLE_WIN_GRAY)
        dialog.resizable(False, False)
        dialog.transient(self.root)
        fields = [
            ("ROM Name:", entry.get("internal_name", "")),
            ("File Name:", entry.get("file_name", "")),
            ("Location:", os.path.dirname(entry.get("path", ""))),
            ("Rom Size:", entry.get("rom_size", _format_rom_size(entry.get("size", 0)))),
            ("Cartridge ID:", header.cart_id),
            ("Release Version:", f"0x{header.release:08X}"),
            ("Clock Rate:", f"0x{header.clock_rate:08X}"),
            ("Country:", entry.get("country", "Unknown")),
            ("CRC1:", f"{header.crc1:08X}"),
            ("CRC2:", f"{header.crc2:08X}"),
            ("CIC Chip:", _CIC_NAMES.get(entry.get("cic"), "Unknown")),
        ]
        group = tk.LabelFrame(dialog, text="", bg=CATHLE_WIN_GRAY, font=UI_FONT)
        group.pack(fill=tk.BOTH, expand=True, padx=8, pady=(7, 3))
        for row, (label, value) in enumerate(fields):
            tk.Label(group, text=label, bg=CATHLE_WIN_GRAY, font=UI_FONT,
                     anchor=tk.W, width=17).grid(row=row, column=0, sticky="w", padx=(5, 2), pady=2)
            box = tk.Entry(group, font=UI_FONT, relief=tk.SUNKEN, bd=1, width=48)
            box.insert(0, value)
            box.configure(state="readonly", readonlybackground="#ffffff")
            box.grid(row=row, column=1, sticky="ew", padx=(2, 5), pady=2)
        tk.Button(dialog, text="Close", width=12, font=UI_FONT,
                  command=dialog.destroy).pack(side=tk.RIGHT, padx=9, pady=(2, 8))

    def show_settings(self, initial_tab="Options"):
        dialog = tk.Toplevel(self.root)
        dialog.title("Settings")
        dialog.geometry("525x365")
        dialog.minsize(500, 340)
        dialog.configure(bg=CATHLE_WIN_GRAY)
        dialog.transient(self.root)
        notebook = ttk.Notebook(dialog)
        notebook.pack(fill=tk.BOTH, expand=True, padx=7, pady=7)
        tabs = {}
        for name in ("Options", "Directories", "Plugins"):
            tab = tk.Frame(notebook, bg=CATHLE_WIN_GRAY)
            notebook.add(tab, text=name)
            tabs[name] = tab
        if initial_tab in tabs:
            notebook.select(tabs[initial_tab])

        options = tabs["Options"]
        core_box = tk.LabelFrame(options, text=" Core Defaults ", bg=CATHLE_WIN_GRAY, font=UI_FONT)
        core_box.pack(fill=tk.X, padx=9, pady=9)
        tk.Label(core_box, text="CPU core style:", bg=CATHLE_WIN_GRAY,
                 font=UI_FONT).grid(row=0, column=0, sticky="w", padx=8, pady=7)
        ttk.Combobox(core_box, values=("Interpreter", "Cached Interpreter"),
                     state="readonly", width=25).grid(row=0, column=1, padx=8, pady=7)
        tk.Checkbutton(options, text="Start Emulation when rom is opened?",
                       variable=self.start_on_open_var, bg=CATHLE_WIN_GRAY,
                       font=UI_FONT).pack(anchor="w", padx=13, pady=3)
        tk.Checkbutton(options, text="Limit FPS", variable=self.limit_fps_var,
                       command=self._sync_options, bg=CATHLE_WIN_GRAY,
                       font=UI_FONT).pack(anchor="w", padx=13, pady=3)
        tk.Checkbutton(options, text="Show CPU usage %", variable=self.show_cpu_var,
                       bg=CATHLE_WIN_GRAY, font=UI_FONT).pack(anchor="w", padx=13, pady=3)

        directories = tabs["Directories"]
        rom_box = tk.LabelFrame(directories, text=" Rom Directory ",
                                bg=CATHLE_WIN_GRAY, font=UI_FONT)
        rom_box.pack(fill=tk.X, padx=9, pady=9)
        directory_entry = tk.Entry(rom_box, textvariable=self.rom_directory_var,
                                   font=UI_FONT, relief=tk.SUNKEN)
        directory_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=7, pady=9)
        tk.Button(rom_box, text="...", width=3, font=UI_FONT,
                  command=self.choose_rom_directory).pack(side=tk.LEFT, padx=(0, 7), pady=9)
        for label in ("N64 Auto saves:  In-memory (single-file mode)",
                      "Instant saves:  In-memory slots",
                      "Screenshots:  Ask when captured"):
            tk.Label(directories, text=label, bg=CATHLE_WIN_GRAY,
                     font=UI_FONT, anchor=tk.W).pack(fill=tk.X, padx=15, pady=5)

        plugins = tabs["Plugins"]
        plugin_values = (
            ("Graphics:", "Built-in VI RGB5551"),
            ("Audio:", "Built-in AI timing"),
            ("Controller:", "Keyboard input"),
            ("Reality Signal Processor:", "Built-in RSP scaffold"),
        )
        for row, (label, value) in enumerate(plugin_values):
            box = tk.LabelFrame(plugins, text=f" {label} ", bg=CATHLE_WIN_GRAY, font=UI_FONT)
            box.pack(fill=tk.X, padx=9, pady=(7 if row == 0 else 2, 2))
            combo = ttk.Combobox(box, values=(value,), state="readonly")
            combo.set(value)
            combo.pack(fill=tk.X, padx=7, pady=5)

        buttons = tk.Frame(dialog, bg=CATHLE_WIN_GRAY)
        buttons.pack(fill=tk.X, padx=7, pady=(0, 7))

        def apply_settings(close=False):
            self.limit_fps = bool(self.limit_fps_var.get())
            new_dir = self.rom_directory_var.get().strip()
            if new_dir and os.path.isdir(new_dir) and new_dir != self.browser.directory:
                self.browser.scan_roms(new_dir)
            self._set_status("Settings applied")
            if close:
                dialog.destroy()

        tk.Button(buttons, text="OK", width=10, font=UI_FONT,
                  command=lambda: apply_settings(True)).pack(side=tk.RIGHT, padx=3)
        tk.Button(buttons, text="Cancel", width=10, font=UI_FONT,
                  command=dialog.destroy).pack(side=tk.RIGHT, padx=3)
        tk.Button(buttons, text="Apply", width=10, font=UI_FONT,
                  command=apply_settings).pack(side=tk.RIGHT, padx=3)

    def show_registers(self):
        if not self.core.rom:
            return
        dialog = tk.Toplevel(self.root)
        dialog.title("R4300i Registers")
        dialog.geometry("460x520")
        tree = ttk.Treeview(dialog, columns=("register", "value"), show="headings")
        tree.heading("register", text="Register")
        tree.heading("value", text="Value")
        tree.column("register", width=170)
        tree.column("value", width=250)
        tree.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        def refresh():
            for item in tree.get_children():
                tree.delete(item)
            with self._core_lock:
                for index, value in enumerate(self.core.cpu.gpr):
                    tree.insert("", tk.END, values=(f"GPR r{index:02d}", f"0x{value:016X}"))
                tree.insert("", tk.END, values=("PC", f"0x{self.core.cpu.pc:08X}"))
                tree.insert("", tk.END, values=("HI", f"0x{self.core.cpu.hi:016X}"))
                tree.insert("", tk.END, values=("LO", f"0x{self.core.cpu.lo:016X}"))
                for index, value in enumerate(self.core.cpu.cp0):
                    name = R4300_CP0_REG_NAMES.get(index, f"CP0 {index}")
                    tree.insert("", tk.END, values=(name, f"0x{value:08X}"))
        refresh()
        tk.Button(dialog, text="Refresh", command=refresh, font=UI_FONT,
                  width=10).pack(side=tk.RIGHT, padx=6, pady=(0, 6))

    def show_memory(self):
        if not self.core.rom:
            return
        dialog = tk.Toplevel(self.root)
        dialog.title("Memory")
        dialog.geometry("720x430")
        controls = tk.Frame(dialog, bg=CATHLE_WIN_GRAY)
        controls.pack(fill=tk.X)
        tk.Label(controls, text="Address:", bg=CATHLE_WIN_GRAY,
                 font=UI_FONT).pack(side=tk.LEFT, padx=(6, 2), pady=6)
        address = tk.Entry(controls, font=UI_FONT_MONO, width=14)
        address.insert(0, "80000000")
        address.pack(side=tk.LEFT, pady=6)
        output = tk.Text(dialog, font=UI_FONT_MONO, bg="#ffffff", fg="#000000",
                         wrap=tk.NONE, relief=tk.SUNKEN)
        output.pack(fill=tk.BOTH, expand=True, padx=5, pady=(0, 5))

        def refresh():
            try:
                virtual = int(address.get().strip().replace("0x", ""), 16)
            except ValueError:
                return
            physical = self.core.bus.v_to_p(virtual)
            lines = []
            with self._core_lock:
                for row in range(16):
                    start = physical + row * 16
                    chunk = self.core.rdram[start:start + 16] if 0 <= start < RDRAM_SIZE else b""
                    hexes = " ".join(f"{value:02X}" for value in chunk).ljust(47)
                    ascii_text = "".join(chr(value) if 32 <= value < 127 else "." for value in chunk)
                    lines.append(f"{(virtual + row * 16) & MASK_32:08X}  {hexes}  {ascii_text}")
            output.delete("1.0", tk.END)
            output.insert("1.0", "\n".join(lines))
        tk.Button(controls, text="View", command=refresh, width=8,
                  font=UI_FONT).pack(side=tk.LEFT, padx=4, pady=6)
        refresh()

    def show_tlb(self):
        if not self.core.rom:
            return
        dialog = tk.Toplevel(self.root)
        dialog.title("TLB")
        dialog.geometry("760x430")
        columns = ("index", "vpn2", "mask", "asid", "pfn0", "pfn1", "valid")
        tree = ttk.Treeview(dialog, columns=columns, show="headings")
        for key in columns:
            tree.heading(key, text=key.upper())
            tree.column(key, width=95, anchor=tk.CENTER)
        tree.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)
        with self._core_lock:
            for index, entry in enumerate(self.core.cpu.tlb):
                tree.insert("", tk.END, values=(
                    index, f"{entry.vpn2:05X}", f"{entry.mask:08X}", entry.asid,
                    f"{entry.pfn0:05X}", f"{entry.pfn1:05X}",
                    f"{int(entry.v0)}/{int(entry.v1)}"
                ))

    def set_breakpoint(self):
        value = simpledialog.askstring("Set Breakpoint", "Virtual address (hex):",
                                       parent=self.root)
        if value:
            try:
                address = int(value.replace("0x", ""), 16) & MASK_32
                self._set_status(f"Breakpoint display set at 0x{address:08X}")
            except ValueError:
                messagebox.showerror("Set Breakpoint", "Enter a hexadecimal address.")

    def show_cheats(self):
        if not self.core.rom:
            return
        dialog = tk.Toplevel(self.root)
        dialog.title("Cheats")
        dialog.geometry("500x340")
        frame = tk.Frame(dialog, bg=CATHLE_WIN_GRAY)
        frame.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)
        listing = tk.Listbox(frame, font=UI_FONT, bg="#ffffff", selectbackground=CATHLE_LIST_SEL_BG,
                             selectforeground=CATHLE_LIST_SEL_FG)
        listing.pack(fill=tk.BOTH, expand=True)

        def refresh():
            listing.delete(0, tk.END)
            for cheat in self.core.cheat_engine.codes:
                listing.insert(tk.END, f"[{'x' if cheat.enabled else ' '}] {cheat.name}    {cheat.code}")

        def add():
            name = simpledialog.askstring("Add Cheat", "Name:", parent=dialog)
            if not name:
                return
            code = simpledialog.askstring("Add Cheat", "Code (AAAAAAAA VVVVVVVV):",
                                          parent=dialog)
            if code:
                self.core.cheat_engine.add(name, code)
                refresh()

        def toggle():
            selection = listing.curselection()
            if selection:
                self.core.cheat_engine.toggle(selection[0])
                refresh()

        def remove():
            selection = listing.curselection()
            if selection:
                del self.core.cheat_engine.codes[selection[0]]
                self.core.cheat_engine.active = [c for c in self.core.cheat_engine.codes if c.enabled]
                refresh()

        buttons = tk.Frame(frame, bg=CATHLE_WIN_GRAY)
        buttons.pack(fill=tk.X, pady=(5, 0))
        for text, command in (("Add New Cheat...", add), ("Enable/Disable", toggle),
                              ("Delete", remove), ("Close", dialog.destroy)):
            tk.Button(buttons, text=text, command=command, font=UI_FONT).pack(
                side=tk.LEFT, padx=(0, 4))
        refresh()

    def show_about(self):
        messagebox.showinfo(
            "About cathle",
            "cathle 0.1.1\n"
            "N64 R4300i emulator core\n\n"
            "cathle classic interface edition\n"
            "Single-file Python 3.14 build\n\n"
            "Core, tools, browser, and interface\n"
            "presented under the cathle name."
        )

    def _on_close(self):
        self.running = False
        self.core.running = False
        self._worker_stop.set()
        self._worker_wake.set()
        if self.root:
            root = self.root
            self.root = None
            root.destroy()

    def run(self):
        if self.root:
            self.root.mainloop()


def list_implemented_opcodes():
    """Return sorted names of every VR4300 opcode with a live dispatch handler."""
    names = []
    for op, (name, fmt) in PRIMARY_OPS.items():
        if fmt is None:
            continue
        if name == "SPECIAL":
            for f, (n, ff) in SPECIAL_OPS.items():
                if ff is not None and _DISPATCH[_ID_SPECIAL | f] is not None:
                    names.append(n)
        elif name == "REGIMM":
            for rt, (n, ff) in REGIMM_OPS.items():
                if ff is not None and _DISPATCH[_ID_REGIMM | rt] is not None:
                    names.append(n)
        elif name == "COP0":
            for rs, (n, ff) in COP0_RS.items():
                if n == "COP0_CO":
                    for cf, (cn, cff) in COP0_CO.items():
                        if cff is not None and _DISPATCH[_ID_COP0_CO | cf] is not None:
                            names.append(cn)
                elif ff is not None and _DISPATCH[_ID_COP0_RS | rs] is not None:
                    names.append(n)
        elif name == "COP1":
            for rs, (n, ff) in COP1_RS.items():
                if n in ("S", "D", "W", "L"):
                    for f, (fn, ffmt) in COP1_FUNCT.items():
                        if ffmt is not None:
                            names.append(f"{fn}.{n}")
                elif n == "BC1":
                    names.append("BC1")
                elif ff is not None and _DISPATCH[_ID_COP1_RS | rs] is not None:
                    names.append(n)
        else:
            if _DISPATCH[_ID_PRIMARY | op] is not None:
                names.append(name)
    # BC1 dispatch slots
    if any(_DISPATCH[_ID_COP1_BC | rt] is not None for rt in range(4)):
        if "BC1" not in names:
            names.append("BC1")
    return sorted(set(names))


def assert_opcode_table():
    """Every non-reserved primary/special/regimm/cop slot must have a handler."""
    missing = []
    for op, (name, fmt) in PRIMARY_OPS.items():
        if name in ("SPECIAL", "REGIMM", "COP0", "COP1"):
            continue
        if fmt is None:
            # reserved primary — must raise RI
            h = _DISPATCH[_ID_PRIMARY | op]
            if h is None:
                missing.append(f"PRIMARY.{name}")
            continue
        if name in ("COP2", "COP3"):
            if _DISPATCH[_ID_PRIMARY | op] is None:
                missing.append(name)
            continue
        if _DISPATCH[_ID_PRIMARY | op] is None:
            missing.append(name)
    for f, (name, fmt) in SPECIAL_OPS.items():
        if _DISPATCH[_ID_SPECIAL | f] is None:
            missing.append(f"SPECIAL.{name}")
    for rt, (name, fmt) in REGIMM_OPS.items():
        if fmt is None:
            if _DISPATCH[_ID_REGIMM | rt] is None:
                missing.append(f"REGIMM.{name}")
        elif _DISPATCH[_ID_REGIMM | rt] is None:
            missing.append(f"REGIMM.{name}")
    for rs, (name, fmt) in COP0_RS.items():
        if name == "COP0_CO":
            continue
        if fmt is None:
            continue
        if _DISPATCH[_ID_COP0_RS | rs] is None:
            missing.append(f"COP0.{name}")
    for cf, (name, fmt) in COP0_CO.items():
        if fmt is None:
            continue
        if _DISPATCH[_ID_COP0_CO | cf] is None:
            missing.append(f"COP0.{name}")
    for rs, (name, fmt) in COP1_RS.items():
        if name in ("S", "D", "W", "L", "BC1"):
            continue
        if fmt is None:
            continue
        if _DISPATCH[_ID_COP1_RS | rs] is None:
            missing.append(f"COP1.{name}")
    for rt in range(4):
        if _DISPATCH[_ID_COP1_BC | rt] is None:
            missing.append(f"BC1.rt{rt}")
    for fid in (_ID_FPU_S, _ID_FPU_D, _ID_FPU_W, _ID_FPU_L):
        for f in COP1_FUNCT:
            if _DISPATCH[_ID_FPU | (fid << 6) | f] is None:
                missing.append(f"FPU.{fid}.{f:02X}")
    if missing:
        raise AssertionError("Missing dispatch handlers: " + ", ".join(missing[:40]))


def self_test() -> int:
    assert_opcode_table()
    names = list_implemented_opcodes()
    # Smoke-test a handful of handlers through the CPU.
    core = ACsN64Core()
    cpu = core.cpu
    g = cpu.gpr
    # LUI + ORI
    cpu.execute(N64Opcode(0x3C010123)); assert (g[1] & MASK_32) == 0x01230000
    cpu.execute(N64Opcode(0x34215678)); assert (g[1] & MASK_32) == 0x01235678
    # ADDU
    g[2] = 5; g[3] = 7
    cpu.execute(N64Opcode(0x00431021)); assert sign32(g[2]) == 12
    # FPU CVT.S.W + ADD.S
    cpu.cp0[CP0_STATUS] |= STATUS_CU1
    cpu.fpr[0] = u64(4)  # word 4
    cpu.execute(N64Opcode(0x46800020))  # CVT.S.W f0, f0  (fmt=W=20? rs=0x14 -> W, funct=0x20)
    # BC1 dispatch must not RI
    cpu.fcr31 |= (1 << FCR31_COND_BIT)
    old_pc = cpu.pc
    cpu.next_pc = u32(old_pc + 4)
    cpu.execute(N64Opcode(0x45010004))  # BC1T +4
    # RECIP.S present in table
    assert any(n.startswith("RECIP") for n in names)
    assert any(n.startswith("RSQRT") for n in names)
    assert "ERET" in names and "CACHE" in names and "SYNC" in names and "WAIT" in names
    # UltraHLE OP_PATCH / OP_GROUP surface
    assert "PATCH" in names and "GROUP" in names
    assert len(ULTRAHLE_PATCH_TABLE) >= 61
    assert set(ULTRAHLE_PATCH_TABLE) == set(ULTRAHLE_PATCH_NAMES)
    # PATCH(4)=__ll_mul / dmultu: A0:A1 * A2:A3 -> V0:V1
    g[_UH_A0], g[_UH_A1] = 0, 6
    g[_UH_A2], g[_UH_A3] = 0, 7
    g[_UH_RA] = 0x80001000
    cpu.pc = 0x80000000; cpu.next_pc = 0x80000004
    cpu.execute(N64Opcode(make_ultrahle_patch(4)))
    assert g[_UH_V0] == 0 and g[_UH_V1] == 42
    assert cpu.pc == 0x80001000 and cpu.next_pc == 0x80001004
    # PATCH(56)=memcpy
    core.rdram[0:8] = b"\x11\x22\x33\x44\x55\x66\x77\x88"
    g[_UH_A0], g[_UH_A1], g[_UH_A2] = 0x80000010, 0x80000000, 8
    g[_UH_RA] = 0x80002000
    cpu.pc = 0x80000000; cpu.next_pc = 0x80000004
    cpu.execute(N64Opcode(make_ultrahle_patch(56)))
    assert bytes(core.rdram[0x10:0x18]) == b"\x11\x22\x33\x44\x55\x66\x77\x88"
    # PATCH(57)=osEepromProbe + PATCH(59/58) write/read round-trip
    core.save_mgr.save_type = SAVE_EEPROM_4K
    core.save_mgr.eeprom[:] = bytearray(EEPROM_16K_SIZE)
    g[_UH_RA] = 0x80003000
    cpu.pc = 0x80000000; cpu.next_pc = 0x80000004
    cpu.execute(N64Opcode(make_ultrahle_patch(57)))
    assert g[_UH_V0] == EEPROM_TYPE_4K
    core.rdram[0x40:0x48] = b"\xDE\xAD\xBE\xEF\xCA\xFE\xF0\x0D"
    g[_UH_A1], g[_UH_A2] = 3, 0x80000040
    g[_UH_RA] = 0x80003000
    cpu.pc = 0x80000000; cpu.next_pc = 0x80000004
    cpu.execute(N64Opcode(make_ultrahle_patch(59)))
    assert g[_UH_V0] == 0
    core.rdram[0x50:0x58] = b"\x00" * 8
    g[_UH_A1], g[_UH_A2] = 3, 0x80000050
    g[_UH_RA] = 0x80003000
    cpu.pc = 0x80000000; cpu.next_pc = 0x80000004
    cpu.execute(N64Opcode(make_ultrahle_patch(58)))
    assert g[_UH_V0] == 0
    assert bytes(core.rdram[0x50:0x58]) == b"\xDE\xAD\xBE\xEF\xCA\xFE\xF0\x0D"
    # GROUP is a no-op
    cpu.pc = 0x80000000; cpu.next_pc = 0x80000004
    cpu.execute(N64Opcode(u32((ULTRAHLE_OP_GROUP << 26) | 1)))
    assert cpu.pc == 0x80000004
    # install_patch helper writes the UltraHLE encoding
    core.ultrahle.install_patch(0x80000100, 23)
    assert core.bus.read_u32(0x80000100) == make_ultrahle_patch(23)
    # UltraHLE SYM / OSCALL database present
    assert len(ULTRAHLE_OSCALL) >= 200
    assert len(ULTRAHLE_OSPATCH) >= 50
    assert "osPiStartDma" not in ULTRAHLE_DISABLE_PATCHES
    assert ultrahle_match_ini("SUPER MARIO 64")["ismario"] == 1
    assert ultrahle_match_ini("Banjo-Kazooie")["bootloader"] == 1
    assert any(e[3] == 57 for e in ULTRAHLE_OSCALL if "osEepromProbe" in e[4])
    # IPL3 HLE must DMA cart[0x1000..] → RDRAM[entry], not a 1:1 rom copy.
    boot_rom = bytearray(0x2000)
    boot_rom[0:4] = Z64_MAGIC
    put_be32(boot_rom, 0x08, 0x80000400)
    boot_rom[0x20:0x34] = b"BOOTTEST\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"
    put_be32(boot_rom, 0x1000, 0x3C1D8040)  # lui sp, 0x8040
    put_be32(boot_rom, 0x1004, 0x27BDFFF0)  # addiu sp, sp, -16
    core.rom = boot_rom
    core.rom_header = N64Header(boot_rom)
    core.cic = CIC_NUS_6102
    core._hle_ipl3_boot()
    assert be32(core.rdram, 0x400) == 0x3C1D8040
    assert be32(core.rdram, 0x404) == 0x27BDFFF0
    assert core.cpu.pc == 0x80000400
    assert core.bus.read_u32(0x80000400) == 0x3C1D8040
    core.cpu.execute(N64Opcode(core.bus.read_u32(core.cpu.pc)))
    assert (core.cpu.gpr[29] & MASK_32) == 0x80400000
    # 60 Hz frame pacing: one step_frame must raise VI and finish under ~2 frame periods.
    core.running = True
    t0 = time.perf_counter()
    steps = core.step_frame(budget_s=0.01)
    dt = time.perf_counter() - t0
    assert steps >= INTERP_MIN_STEPS
    assert core.frame_count >= 1
    assert core.bus.hw_interrupts & MI_INTR_VI
    assert dt < FRAME_PERIOD_NTSC * 3
    assert abs(core.frame_period - FRAME_PERIOD_NTSC) < 1e-6
    # COMPARE must arm IP7 only (never a fake SP interrupt).
    core.cpu.cp0[CP0_COMPARE] = u32(core.cpu.cp0[CP0_COUNT] + 1)
    core.cpu.cp0[CP0_CAUSE] &= ~CAUSE_IP7
    core.bus.hw_interrupts &= ~MI_INTR_SP
    core.cpu.step()
    assert core.cpu.cp0[CP0_CAUSE] & CAUSE_IP7
    assert not (core.bus.hw_interrupts & MI_INTR_SP)
    print(f"{APP_NAME}: opcode self-test passed ({len(names)} named ops, "
          f"{len(ULTRAHLE_PATCH_TABLE)} UltraHLE patches, "
          f"{steps} steps/frame @ {1.0/max(dt,1e-6):.0f} target-Hz capable, dispatch complete)")
    return 0


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if "--self-test" in argv or "--opcodes" in argv:
        if "--opcodes" in argv:
            assert_opcode_table()
            print("\n".join(list_implemented_opcodes()))
            return 0
        return self_test()
    if not tk:
        print("Tkinter not available — running headless self-test")
        return self_test()
    app = CathleApp()
    app.run()
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
