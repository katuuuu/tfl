import os
from config import config
from typess import Automata, LTable




def add_leading_spaces(e: str, count: int) -> str:
    spaces = count - len(e)
    return f"{' ' * spaces}{e}"

def print_automata(automata: Automata) -> str:
    states_line = f"*STATES*: {' '.join(map(str, range(len(automata['states']))))}"
    init_line = f"*INIT*: {automata['init']}"
    final_line = f"*FINAL*: {' '.join(map(str, automata['final']))}"
    alphabet_line = f"*ALPHABET*: {' '.join(automata['alphabet'])}"

    column_sizes = [max(max(map(len, row.values()), default=0), 1) for row in automata['map']]
    header = '\n /      ' + '       '.join(automata['alphabet'])
    table_string = ''
    for i, dist in enumerate(automata['map']):
        row = [str(i)]
        for symb in automata['alphabet']:
            if symb in dist:
                row.append(str(dist[symb][0]))
            else:
                row.append(' ')
        table_string += f"{'       '.join(row)}\n"

    return f"{states_line}\n{init_line}\n{final_line}\n{alphabet_line}\n{header}\n{'-' * 40}\n{table_string}"



