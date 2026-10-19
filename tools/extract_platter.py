"""
Extractor and RPN bytecode inspection/decompiler utility for Niakwa BASIC-2 PLATTER1.BS2.
Extracts the catalog, MRPARAMS parameter record, and readable program listings into extracted_basic/.
"""
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PLATTER_PATH = ROOT / "PLATTER1.BS2"
OUT_DIR = ROOT / "extracted_basic"


def decode_wang_bcd_float(buf: bytes) -> float:
    """Decode an 8-byte or 9-byte Wang 2200 BCD floating-point number."""
    # In MRPARAMS data blocks, each numeric entry is 9 bytes: [0x08, sign/exp, bcd_mantissa(7 bytes)]
    if len(buf) == 9 and buf[0] == 0x08:
        buf = buf[1:]
    if len(buf) != 8 or all(b == 0 for b in buf):
        return 0.0
    sign_exp = buf[0]
    exp_byte = buf[1]
    # Digits are 14 nibbles in buf[1..7] or buf[2..7]:
    # Wait: earlier we saw:
    # 08 03 01 64 40 00 00 00 00 -> 1644.0 (exp=03 -> 10^3, mantissa=1.644000000000)
    # 08 01 07 95 00 00 00 00 00 -> 79.50  (exp=01 -> 10^1, mantissa=7.950000000000)
    # 08 04 02 22 65 00 00 00 00 -> 22265  (exp=04 -> 10^4, mantissa=2.226500000000)
    # 08 00 01 00 00 00 00 00 00 -> 1.0    (exp=00 -> 10^0, mantissa=1.000000000000)
    exp = sign_exp & 0x7F
    if sign_exp & 0x80:
        exp = -exp
    digits = []
    for b in buf[1:]:
        digits.append((b >> 4) & 0xF)
        digits.append(b & 0xF)
    # First nibble of buf[1] is sign of mantissa/exponent flags, second nibble is first digit
    mant_sign = -1.0 if (digits[0] & 0x8) else 1.0
    if digits[0] & 0x1:
        exp = -exp
    mant_str = f"{digits[1]}." + "".join(str(d) for d in digits[2:])
    try:
        return mant_sign * float(mant_str) * (10.0 ** exp)
    except ValueError:
        return 0.0


def parse_catalog(data: bytes):
    catalog = []
    for s in range(24):
        sec = data[s * 256 : (s + 1) * 256]
        for i in range(0, 256, 16):
            if s == 0 and i == 0:
                continue
            rec = sec[i : i + 16]
            if rec[0] == 0x10 and any(rec[8:]):
                ftype = rec[1]
                start_s = (rec[2] << 8) | rec[3]
                end_s = (rec[4] << 8) | rec[5]
                name = rec[8:16].decode("ascii", errors="replace").strip()
                catalog.append(
                    {
                        "name": name,
                        "type": "PROGRAM" if ftype == 0x80 else "DATA",
                        "type_code": ftype,
                        "start_sector": start_s,
                        "end_sector": end_s,
                        "sectors": end_s - start_s + 1,
                    }
                )
    return catalog


def extract_mrparams(data: bytes, start_s: int, end_s: int):
    raw = data[start_s * 256 : (end_s + 1) * 256]
    # Data sectors in Wang BASIC-2 start with 0x82 <rec_num> (or 0x81/0xa0)
    # Strip sector headers (2 bytes at start of each 256-byte sector and trailing 0xfd padding)
    payload = bytearray()
    for s in range(end_s - start_s + 1):
        sec = raw[s * 256 : (s + 1) * 256]
        if sec[0] in (0x81, 0x82):
            # Find end of valid data in sector (marked by 0xfd)
            body = sec[2:]
            payload.extend(body)

    # Parse strings (prefixed by 0x80 | length or 0xc0 for 64-byte string) and numbers (prefixed by 0x08)
    strings = []
    numbers = []
    i = 0
    while i < len(payload):
        b = payload[i]
        if b == 0xFD or b == 0x00:
            i += 1
            continue
        if b == 0x01 and i + 1 < len(payload) and payload[i + 1] == 0xC0:
            # 64-byte string B$
            s_val = payload[i + 2 : i + 66].decode("ascii", errors="replace")
            strings.append(s_val)
            i += 66
        elif 0x81 <= b <= 0xBF:
            slen = b & 0x3F
            s_val = payload[i + 1 : i + 1 + slen].decode("ascii", errors="replace")
            strings.append(s_val)
            i += 1 + slen
        elif b == 0x08 and i + 9 <= len(payload):
            val = decode_wang_bcd_float(payload[i : i + 9])
            numbers.append(val)
            i += 9
        else:
            i += 1

    return {
        "B$": strings[0].strip() if len(strings) > 0 else "",
        "A1$": strings[1].strip() if len(strings) > 1 else "",
        "J$": [s.strip() for s in strings[2:12]],
        "H$": [s.strip() for s in strings[12:32]],
        "I$": [s.strip() for s in strings[32:62]],
        "H": numbers[:37],
    }


def extract_prog_lines(data: bytes, start_s: int, end_s: int):
    raw = data[start_s * 256 : (end_s + 1) * 256]
    hdr_len = raw[0] | (raw[1] << 8)
    compiler_ver = raw[2 : 2 + hdr_len].decode("ascii", errors="replace")
    pos = 2 + hdr_len
    lines = []
    while pos + 4 <= len(raw):
        b0, b1 = raw[pos], raw[pos + 1]
        if b0 == 0xFF and b1 == 0xFF:
            break
        line_num = (
            (b1 >> 4) * 1000
            + (b1 & 0xF) * 100
            + (b0 >> 4) * 10
            + (b0 & 0xF)
        )
        length = raw[pos + 2] | (raw[pos + 3] << 8)
        if pos + 4 + length > len(raw):
            break
        body = raw[pos + 4 : pos + 4 + length]
        lines.append((line_num, body))
        pos += 4 + length
    return compiler_ver, lines


def main():
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    with open(PLATTER_PATH, "rb") as f:
        data = f.read()

    catalog = parse_catalog(data)
    with open(OUT_DIR / "catalog.json", "w", encoding="utf-8") as f:
        json.dump(catalog, f, indent=2)

    for entry in catalog:
        name = entry["name"]
        s1, s2 = entry["start_sector"], entry["end_sector"]
        if entry["type"] == "DATA" and name == "MRPARAMS":
            params = extract_mrparams(data, s1, s2)
            with open(OUT_DIR / "MRPARAMS_platter.json", "w", encoding="utf-8") as f:
                json.dump(params, f, indent=2)
            print(f"Extracted MRPARAMS: Factory={params['B$']!r}, CropStart={params['A1$']!r}")
        elif entry["type"] == "PROGRAM":
            ver, lines = extract_prog_lines(data, s1, s2)
            out_file = OUT_DIR / f"{name}.rpn.txt"
            with open(out_file, "w", encoding="utf-8") as f:
                f.write(f"# Program: {name} | Compiler: {ver} | Sectors: 0x{s1:04x}..0x{s2:04x}\n")
                for lnum, body in lines:
                    asc = "".join(chr(b) if 32 <= b < 127 else f"[{b:02x}]" for b in body)
                    f.write(f"{lnum:04d}: {asc}\n")
            print(f"Extracted {name:8s} ({len(lines):3d} lines)")


if __name__ == "__main__":
    main()
