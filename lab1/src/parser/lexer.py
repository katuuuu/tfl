import re
import os
from dataclasses import dataclass

from parser.praser_config import *


@dataclass
class Token:
    typ: str
    value: str

    def __repr__(self):
        return self.value or self.typ or 'EOF_TOKEN' 


def lexer(raw: str) -> list[Token]:
    if os.path.exists(raw):
        with open(raw) as f:
            raw = f.read()

    tokens = []

    while raw:
        for lexem_type, pattern, func in LEXEM_TYPES:
            match = re.findall(pattern, raw)
            if match:
                result = match[0]
                attr = func(result)
                
                if lexem_type != SKIP:
                    tokens.append(Token(lexem_type, attr))

                raw = raw[len(result):]
                break

        else:
            raise RuntimeError(f'невозможно токенизировать файл: "{raw[:10]}"')

    return tokens