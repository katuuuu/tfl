import os
import argparse
from typing import Iterable
import subprocess

from utils.trs_checker import TrsChecker
from parser.parser import Parser
from models.trs_models import Rule

from translators.trs_to_linsp_translator import LinspTranslator
from translators.linsp_to_ineq_translator import IneqTranslator
from translators.ineq_to_smt_translator import SmtTranslator


def call_solver(file: str):
    solver_process = subprocess.run(
        ['z3', '-smt2', file],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    retcode = solver_process.returncode
    stdout = solver_process.stdout.decode("utf-8") 
    
    if retcode != 0:
        raise RuntimeError(f'z3 retcode = {retcode}:\n{stdout}')

    match stdout:
        case 'sat\n':
            return True
        case 'unsat\n':
            return False
        case _:
            raise RuntimeError(f'unknown z3 output: {stdout}')


def check_sat(rules: list[Rule], variables:set[str], debug=False): 
    def draw_line():
        print('*'*40)

    def debug_print(seq: Iterable, header:str):
        draw_line()
        print(header)
        for elem in seq:
            print(elem)
        draw_line()
        print()

    if debug:
        debug_print(rules,'TRS parsed:')
    
    # проверяем корректность TRS
    TrsChecker(variables, rules).check()

    # переводим TRS в линейные функции0
    linsp_trs = LinspTranslator.trs_to_linsp(rules, variables)
    if debug:
        debug_print(linsp_trs, 'TRS linear approx:')

    # переводим неравенства линейных функций
    # в системы неравенств по коэффициентам
    ineqs = IneqTranslator.linsp_to_ineq(linsp_trs)
    if debug:
        debug_print(ineqs, 'Twin ineq systems:')

    # транслируем в SMT2
    smt_translator = SmtTranslator().build_smt_repr(ineqs)
    if debug:
        smt_translator.print_smt2()

    # записываем smt-условия в файл
    file = './linear_aprox.smt2'
    smt_translator.record_to_file(file)

    # вызываем солвер
    solver_res = call_solver(file)
    return 'SAT' if solver_res else 'UNSAT'


if __name__ == '__main__':
    parser = argparse.ArgumentParser(prog = 'TRS Checker')
    parser.add_argument('mode', 
                        choices=['one-file', 'many-files'], 
                        default='one-file',
                        help='"one-file" - читает TRS из файла\n'+
                            '"many-files - запускает все тесты в директории"')

    parser.add_argument('filedir', 
                        help='файл, из которого происходит чтение TRS, \n' + \
                            'используется при mode="one-file" \n' + \
                            'или директория с тестами,\n' + \
                            'при mode = "many-files"')
    
    args = parser.parse_args()


    match args.mode:
        case 'many-files':
            files = os.listdir(args.filedir)
            for file in sorted(files):
                rules, variables = Parser(str(os.path.join(args.filedir, file))).lexemize().parse()  
                print('#TEST {:s}:'.format(file), end=' ')
                try:
                    res = check_sat(rules, variables)
                    print('{:s}'.format(res))
                except AssertionError as e:
                    print(e)

        case 'one-file':
            print(check_sat(*Parser(args.filedir).lexemize().parse(), debug=True))
