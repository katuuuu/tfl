import sys

from settings import G_FILE, W_FILE, G_VERBOSE, DEFAULT_G_FILE, DEFAULT_W_FILE, OUTPUT_TO_FILE, OUTPUT_FILE
from models import Gclass, ProcessSLR

if __name__ == "__main__":
    buffer = ''

    try:
        with open(DEFAULT_G_FILE, "r") as f:
            file_contents = f.readlines()
            grammar_string = "".join(filter(None, file_contents))
    except:
        with open(G_FILE, "r") as f:
            file_contents = f.readlines()
            grammar_string = "".join(filter(None, file_contents))

    try:
        with open(DEFAULT_W_FILE, "r") as f:
            file_contents = f.readlines()
            word = "".join(filter(None, file_contents))
    except:
        with open(W_FILE, "r") as f:
            file_contents = f.readlines()
            word = "".join(filter(None, file_contents))

    if not word:
        word = "a * a + a + a"

    if OUTPUT_TO_FILE:
        buffer += '-' * 50 + '\n'
        buffer += f'Грамматика берется из файла {G_FILE}' + '\n'
        buffer += f'Выражение берется из файла {W_FILE}' + '\n'
        buffer += '-' * 50 + '\n'
    else:
        print('-' * 50)
        print(f'Грамматика берется из файла {G_FILE}')
        print(f'Выражение берется из файла {W_FILE}')
        print('-' * 50)

    G = Gclass(grammar_string)

    slr_parser = ProcessSLR(G)
    if G_VERBOSE:
        if OUTPUT_TO_FILE:
            buffer = slr_parser.data_save(buffer)
        else:
            slr_parser.data_print()

    if OUTPUT_TO_FILE:
        buffer += '-' * 50 + '\n'
        buffer += 'Анализ выражения - ' + '\n'
        buffer += word + '\n'
        buffer += '-' * 50 + '\n'
        buffer += 'Результат разбора строки:' + '\n'
    else:
        print('-' * 50)
        print('Анализ выражения - ')
        print(word)
        print('-' * 50)
        print('Результат разбора строки:')

    results = slr_parser.parse_LR(word)

    if OUTPUT_TO_FILE:
        buffer = slr_parser.LR_save(buffer, results)
    else:
        slr_parser.LR_print(results)

    if OUTPUT_TO_FILE:
        with open(OUTPUT_FILE, "w", encoding='utf-8') as f:
            f.write(buffer)

    sys.exit()
