import config
from type import Automata, LTable
import json

def clear_log():
    with open(config.LOG_PATH, 'w') as log_file:
        log_file.write('')

def log_automata(automata: Automata, label=''):
    with open(config.LOG_PATH, 'a') as log_file:
        log_file.write(f"AUTOMATA({label}): \n{print_automata(automata)}\n\n")

def log_table(l_table: LTable, label=''):
    with open(config.LOG_PATH, 'a') as log_file:
        log_file.write(f"TABLE({label}): \n{print_table(l_table)}\n")

def log(text: str):
    with open(config.LOG_PATH, 'a') as log_file:
        log_file.write(f"{text}\n")

def add_leading_spaces(e: str, count: int) -> str:
    spaces = count - len(e)
    return f"{' ' * spaces}{e}"

def print_automata(automata: Automata) -> str:
    states_line = f"Состояния: {' '.join(map(str, range(automata.states)))}"
    init_line = f"Начальное состояние: {automata.init}"
    final_line = f"Конечные состояния: {' '.join(map(str, automata.final))}"
    alphabet_line = f"Алфавит: {' '.join(automata.alphabet)}"
    
    header_template = "{}\n{} | {}"
    alphabet_str = " | ".join(automata.alphabet)
    header = header_template.format("Таблица переходов:", add_leading_spaces("\\", max(len(str(automata.states - 1)), 1) + 2), alphabet_str)
    
    table_lines = [header]
    separator = '+' + '+'.join(['-' * (max(len(str(automata.states - 1)), 1) + 2)] + ['-' * 3 for _ in automata.alphabet]) + '+'
    table_lines.append(separator)
    
    for i, transitions in enumerate(automata.map):
        transitions_str = " | ".join(' '.join(str(state) for state in transitions[symbol]) if transitions[symbol] else ' ' for symbol in automata.alphabet)
        line = f"| {i}{' ' * (max(len(str(automata.states - 1)), 1) - len(str(i)))} | {transitions_str} |"
        table_lines.append(line)
        table_lines.append(separator)
    
    table_str = "\n".join(table_lines)
    return f"{states_line}\n{init_line}\n{final_line}\n{alphabet_line}\n{table_str}"

def print_table(table):
    # ширина первого столбца (для состояний S и extS)
    state_column_width = max(len(state) for state in table.S + table.extS) + 1

    # ширина каждого столбца E
    event_column_widths = [len(event) + 2 for event in table.E]

    # заголовок таблицы
    header_pieces = [' ' * state_column_width] 
    for event, width in zip(table.E, event_column_widths):
        header_pieces.append(f"{event: <{width}}") 
    header = ''.join(header_pieces)

    # формируем строки таблицы для основных состояний S
    main_body_lines = []
    for state, transitions in zip(table.S, table.table):
        line_pieces = [f"{state: <{state_column_width}}"]  # название 
        for value, width in zip(transitions, event_column_widths):
            # '1' или '0' в зависимости от перехода
            line_pieces.append(f"{'1' if value else '0': <{width}}")
        main_body_lines.append(''.join(line_pieces))

    # расширенное состояние extS
    extended_body_lines = []
    for ext_state, ext_transitions in zip(table.extS, table.extTable):
        line_pieces = [f"{ext_state: <{state_column_width}}"]
        for value, width in zip(ext_transitions, event_column_widths):
            line_pieces.append(f"{'1' if value else '0': <{width}}")
        extended_body_lines.append(''.join(line_pieces))

    # соединяем
    separator = '-' * len(header)  # разделяем линией 
    formatted_table = f"{header}\n{''.join(main_body_lines)}\n{separator}\n{''.join(extended_body_lines)}"
    
    return formatted_table
