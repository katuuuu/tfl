# -- coding: utf-8 --
"""
Реализовать Generic SLR(1)-разбор слова w по грамматике G
с использованием графовидного стека. Входные данные:
грамматика G (произвольная КС-грамматика без ε-правил),
слово w, а также опционально— шаг n разбора, для
которого необходимо отрисовать графовидный стек.
Результат работы программы: сообщение об успешном
разборе строки с предъявлением (по необходимости) графа
разбора на n-ом шаге, либо сообщение о неуспешном
разборе с указанием первой найденной ошибочной позиции
(то есть такой, в которой невозможен ни один из путей
разбора).
n-ый шаг здесь —состояние стека после n действий
(действие —перенос (reduce) или свёртка (shift)), а не
состояние стека после чтения n букв.
"""

import pandas as pd


class Gclass:
    def __init__(self, grammar_string):
        self.grammar_string = grammar_string
        self.grammar = {}
        self.start = None
        self.terms = set()
        self.nonterms = set()

        for prod in list(filter(None, grammar_string.splitlines())):
            head, _, bodies = prod.partition(" -> ")

            if not head.isupper():
                # print("jj", head, bodies)
                raise ValueError(
                    f"'{head} -> {bodies}': Заголовок '{head}' должен быть в верхнем регистре для анализа в качестве нетерминала"
                )

            if not self.start:
                self.start = head

            self.grammar.setdefault(head, set())
            self.nonterms.add(head)
            bodies = {
                tuple(body.split()) for body in " ".join(bodies.split()).split("|")
            }

            for body in bodies:
                if "^" in body and body != ("^",):
                    raise ValueError(
                        f'\'{head} -> {" ".join(body)}\': Null символ \'^\' не допустим в этом месте'
                    )

                self.grammar[head].add(body)

                for symbol in body:
                    if not symbol.isupper() and symbol != "^":
                        self.terms.add(symbol)
                    elif symbol.isupper():
                        self.nonterms.add(symbol)

        self.symbols = self.terms | self.nonterms

        # print("Старт\n\n", self.start)
        # print("Терминалы\n\n", self.terms)
        # print("Нетерминалы\n\n", self.nonterms)


def first_step_process(G):
    def union(set_1, set_2):
        set_1_len = len(set_1)
        set_1 |= set_2

        return set_1_len != len(set_1)

    first = {symbol: set() for symbol in G.symbols}
    first.update((terminal, {terminal}) for terminal in G.terms)
    follow = {symbol: set() for symbol in G.nonterms}
    follow[G.start].add("$")

    while True:
        updated = False

        for head, bodies in G.grammar.items():
            for body in bodies:
                for symbol in body:
                    if symbol != "^":
                        updated |= union(first[head], first[symbol] - set("^"))

                        if "^" not in first[symbol]:
                            break
                    else:
                        updated |= union(first[head], set("^"))
                else:
                    updated |= union(first[head], set("^"))

                aux = follow[head]
                for symbol in reversed(body):
                    if symbol == "^":
                        continue
                    if symbol in follow:
                        updated |= union(follow[symbol], aux - set("^"))
                    if "^" in first[symbol]:
                        aux = aux | first[symbol]
                    else:
                        aux = first[symbol]

        if not updated:
            return first, follow


class ProcessSLR:
    def __init__(self, G):
        self.G_prime = Gclass(f"{G.start}' -> {G.start}\n{G.grammar_string}")
        self.max_G_prime_len = len(max(self.G_prime.grammar, key=len))
        self.G_indexed = []

        for head, bodies in self.G_prime.grammar.items():
            for body in bodies:
                self.G_indexed.append([head, body])

        self.first, self.follow = first_step_process(self.G_prime)
        self.C = self.items(self.G_prime)
        self.action = list(self.G_prime.terms) + ["$"]
        self.goto = list(self.G_prime.nonterms - {self.G_prime.start})
        self.parse_table_symbols = self.action + self.goto
        self.parse_table = self.table_process()

    def clos(self, I):
        J = I

        while True:
            item_len = len(J)

            for head, bodies in J.copy().items():
                for body in bodies.copy():
                    if "." in body[:-1]:
                        symbol_after_dot = body[body.index(".") + 1]

                        if symbol_after_dot in self.G_prime.nonterms:
                            for G_body in self.G_prime.grammar[symbol_after_dot]:
                                J.setdefault(symbol_after_dot, set()).add(
                                    (".",) if G_body == ("^",) else (".",) + G_body
                                )

            if item_len == len(J):
                return J

    def go(self, I, X):
        goto = {}

        for head, bodies in I.items():
            for body in bodies:
                if "." in body[:-1]:
                    dot_pos = body.index(".")

                    if body[dot_pos + 1] == X:
                        replaced_dot_body = (
                            body[:dot_pos] + (X, ".") + body[dot_pos + 2 :]
                        )

                        for C_head, C_bodies in self.clos(
                            {head: {replaced_dot_body}}
                        ).items():
                            goto.setdefault(C_head, set()).update(C_bodies)

        return goto

    def items(self, G_prime):
        C = [self.clos({G_prime.start: {(".", G_prime.start[:-1])}})]
        while True:
            item_len = len(C)

            for I in C.copy():
                for X in G_prime.symbols:
                    goto = self.go(I, X)

                    if goto and goto not in C:
                        C.append(goto)

            if item_len == len(C):
                return C

    def table_process(self):
        parse_table = {
            r: {c: "" for c in self.parse_table_symbols} for r in range(len(self.C))
        }

        for i, I in enumerate(self.C):
            for head, bodies in I.items():
                for body in bodies:
                    if "." in body[:-1]:
                        symbol_after_dot = body[body.index(".") + 1]

                        if symbol_after_dot in self.G_prime.terms:
                            s = f"s{self.C.index(self.go(I, symbol_after_dot))}"

                            if s not in parse_table[i][symbol_after_dot]:
                                if "r" in parse_table[i][symbol_after_dot]:
                                    parse_table[i][symbol_after_dot] += "/"

                                parse_table[i][symbol_after_dot] += s

                    elif body[-1] == "." and head != self.G_prime.start:
                        for j, (G_head, G_body) in enumerate(self.G_indexed):
                            if G_head == head and (
                                G_body == body[:-1]
                                or G_body == ("^",)
                                and body == (".",)
                            ):
                                for f in self.follow[head]:
                                    if parse_table[i][f]:
                                        parse_table[i][f] += "/"

                                    parse_table[i][f] += f"r{j}"

                                break

                    else:  # CASE 2 c
                        parse_table[i]["$"] = "acc"

            for A in self.G_prime.nonterms:  # CASE 3
                j = self.go(I, A)

                if j in self.C:
                    parse_table[i][A] = self.C.index(j)

        return parse_table

    def data_print(self):
        def fprint(text, variable):
            print(f'{text:>12}: {", ".join(variable)}')

        print("Дополненная граматика:")

        for i, (head, body) in enumerate(self.G_indexed):
            # print(f'{str(i)}: {head} -> {" ".join(body)}')
            print(f'{head} -> {" ".join(body)}')

        print()
        print("Каноническая коллекция:")
        for i, prods in enumerate(self.C):
            print("----" + str(i) + "----")
            for P in prods:
                for NT in prods[P]:
                    print(P, "->", " ".join(NT))

            print()

        fprint("Терминалы", self.G_prime.terms)
        fprint("Нетерминалы", self.G_prime.nonterms)
        fprint("Символы", self.G_prime.symbols)

        headers = ["Шаги"] * (1 + len(self.G_prime.terms)) + [""] * (
            len(self.G_prime.nonterms) - 1
        )

        print("\nТаблица парсинга:")
        print()
        PARSE_TABLE = pd.DataFrame(self.parse_table).T
        PARSE_TABLE.columns = [headers, list(PARSE_TABLE.columns)]
        print(PARSE_TABLE)

    def data_save(self, buffer):
        def fsave(buffer, text, variable):
            return f'{text:>12}: {", ".join(variable)}' + '\n'

        buffer += "Дополненная граматика:\n"

        for i, (head, body) in enumerate(self.G_indexed):
            buffer += f'{head} -> {" ".join(body)}\n'

        buffer += "\nКаноническая коллекция:\n"

        for i, prods in enumerate(self.C):
            buffer += "----" + str(i) + "----" + "\n"
            for P in prods:
                for NT in prods[P]:
                    buffer += str(P) + "->" + " ".join(NT) + "\n"

            buffer += "\n"

        buffer += fsave(buffer, "Терминалы", self.G_prime.terms)
        buffer += fsave(buffer, "Нетерминалы", self.G_prime.nonterms)
        buffer += fsave(buffer, "Символы", self.G_prime.symbols)

        headers = ["Шаги"] * (1 + len(self.G_prime.terms)) + [""] * (
            len(self.G_prime.nonterms) - 1
        )

        buffer += "\nТаблица парсинга:\n"
        PARSE_TABLE = pd.DataFrame(self.parse_table).T
        PARSE_TABLE.columns = [headers, list(PARSE_TABLE.columns)]
        df_txt = PARSE_TABLE.to_string()
        buffer += df_txt + "\n"

        return buffer

    def parse_LR(self, w):
        buffer = f"{w} $".split()
        pointer = 0
        a = buffer[pointer]
        stack = ["0"]
        symbols = [""]
        results = {
            "шаг": [],
            "стек": [] + stack,
            "символы": [] + symbols,
            "ввод": [],
            "действие": [],
        }

        step = 0
        while True:
            s = int(stack[-1])
            step += 1
            results["шаг"].append(f"{step}")
            results["ввод"].append(" ".join(buffer[pointer:]))

            if a not in self.parse_table[s]:
                results["действие"].append(f"ОШИБКА: нераспознанный символ {a}")

                break

            elif not self.parse_table[s][a]:
                results["действие"].append(
                    "ОШИБКА: слово не может быть разобрана заданным словарем"
                )

                break

            elif "/" in self.parse_table[s][a]:
                action = "reduce" if self.parse_table[s][a].count("r") > 1 else "Терминал в стек"
                results["действие"].append(
                    f"ОШИБКА: {action} - ошибка на шаге {s}, символ {a}"
                )

                break

            elif self.parse_table[s][a].startswith("s"):
                results["действие"].append("Терминал в стек")
                stack.append(self.parse_table[s][a][1:])
                symbols.append(a)
                results["стек"].append(" ".join(stack))
                results["символы"].append(" ".join(symbols))
                pointer += 1
                a = buffer[pointer]

            elif self.parse_table[s][a].startswith("r"):
                head, body = self.G_indexed[int(self.parse_table[s][a][1:])]
                results["действие"].append(f'Свертка(замена) {head} -> {" ".join(body)}')

                if body != ("^",):
                    stack = stack[: -len(body)]
                    symbols = symbols[: -len(body)]

                stack.append(str(self.parse_table[int(stack[-1])][head]))
                symbols.append(head)
                results["стек"].append(" ".join(stack))
                results["символы"].append(" ".join(symbols))

            elif self.parse_table[s][a] == "acc":
                results["действие"].append("Единица трансляции на стеке")

                break

        return results

    def LR_print(self, results):
        df = pd.DataFrame(results)
        print("\n")
        df.set_index('шаг', inplace=True)
        print(df)

    def LR_save(self, buffer, results):
        df = pd.DataFrame(results)
        df.set_index('шаг', inplace=True)
        df_txt = df.to_string()
        return buffer + '\n' + df_txt + '\n'
