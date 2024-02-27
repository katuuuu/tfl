from config import config
from l_table import LTableAlgorithm
from parser import read_input
from typess import Automata, ParsingError
from utils import print_automata


def main():
    for i in range(1,11):
        config["inputPath"] = "test//input" + str(i) + ".txt"
        config["outputPath"] = "test//output" + str(i) + ".txt"
        input_data = read_input()

        # соответствует ли слово регулярке
        def oracle(word):
            return input_data["regex"].match(word) is not None

        l = LTableAlgorithm(input_data["alphabet"], oracle, config["P"], input_data["maxLength"])
        automata = l.compute()
        print_results(automata)



def print_results(automata):
    with open(config["outputPath"], "w") as output_file:
        output_file.write(print_automata(automata))


try:
    main()
except ParsingError as e:
    print(e.message)
except Exception as e:
    raise e
