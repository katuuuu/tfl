from typing import Dict

from typess import Automata, ParsingError


def check_word(word: str, automata: Automata):
    try:
        currentState = automata['init']
        for i, symbol in enumerate(word):
            to = automata['map'][currentState].get(symbol, [])
            if len(to) > 1:
                pass
                #raise ParsingError(f'Non-deterministic automaton at state {currentState} with symbol {symbol}')
            if len(to) == 0:
                return False
            currentState = to[0]
        return automata['final'].count(currentState) > 0
    except ParsingError as e:
        raise ParsingError(f'Error checking word "{word}": {str(e)}')
