"""Bounded decompression of matching proof data, followed by exact replay.

The expanded pairs pass through verify_anchor_matching.py unchanged. Compression
only changes storage; it supplies no mathematical assumption or solver status.
"""
from __future__ import annotations
import argparse
import base64
from hashlib import sha256
import json
from pathlib import Path
import zlib
from verify_anchor_matching import LIMIT, require, read_certificate, verify


def expand_packed(data):
    require(set(data) == {'format', 'region', 'parameters', 'bins', 'pair_stream'},
            'Invalid packed root')
    require(type(data['bins']) is list and 1 <= len(data['bins']) <= 1000,
            'Invalid packed covering')
    require(type(data['pair_stream']) is str and len(data['pair_stream']) <= LIMIT,
            'Invalid packed stream')
    compressed = base64.b64decode(data['pair_stream'], validate=True)
    decoder = zlib.decompressobj()
    stream = decoder.decompress(compressed, 5_000_001)
    require(len(stream) <= 5_000_000 and decoder.eof and
            not decoder.unconsumed_tail and not decoder.unused_data,
            'Invalid or oversized packed compression')
    position = 0

    def number():
        nonlocal position
        result = 0
        for shift in range(0, 35, 7):
            require(position < len(stream), 'Truncated packed integer')
            byte = stream[position]
            position += 1
            require(shift < 28 or byte < 16, 'Packed integer overflow')
            result |= (byte & 127) << shift
            if byte < 128:
                return result
        raise ValueError('Invalid packed integer')

    bins = []
    total = 0
    for item in data['bins']:
        require(type(item) is dict and set(item) == {'width', 'grid'},
                'Invalid packed bin')
        count = number()
        total += count
        require(count <= 32768 and total <= 1_000_000, 'Oversized matching')
        pairs = []
        a = b = 0
        for _ in range(count):
            a += number()
            delta = number()
            b += delta//2 if delta % 2 == 0 else -(delta+1)//2
            require(0 <= a < 65536 and 0 <= b < 65536, 'Packed cell overflow')
            pairs.append([a, b])
        bins.append(dict(width=item['width'], grid=item['grid'], pairs=pairs))
    require(position == len(stream), 'Trailing packed data')
    return dict(format='ambi-anchor-matching-v1', region=data['region'],
                parameters=data['parameters'], bins=bins)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    raw, data = read_certificate(args.certificate)
    require(type(data) is dict and data.get('format') == 'ambi-anchor-matching-packed-v1',
            'Expected packed matching certificate')
    result = verify(expand_packed(data))
    result['certificate_sha256'] = sha256(raw).hexdigest()
    result['packing_source_sha256'] = sha256(Path(__file__).read_bytes()).hexdigest()
    text = json.dumps(result, indent=2)+'\n'
    if args.output:
        args.output.write_text(text, encoding='utf-8')
    print(text, end='')
