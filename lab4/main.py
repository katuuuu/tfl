import DPDA
def main():
    accept5 = DPDA.State(state_type="Accept")
    pop5 = DPDA.State(state_type="Pop")
    pop4 = DPDA.State(state_type="Pop")
    pop3 = DPDA.State(state_type="Pop")
    push2 = DPDA.State(state_type="Push")
    read1 = DPDA.State(state_type="Read")
    trap1 = DPDA.State(state_type="Trap")

    read1.add_transition(push2, character="a")
    read1.add_transition(pop3, character="b")
    read1.add_transition(pop4, character="$")
    read1.add_transition(trap1, character="c")
    read1.add_transition(pop5, character="g")

    push2.add_transition(read1, character="a")
    pop3.add_transition(read1, character="a")
    pop5.add_transition(read1, character="g")
    push2.add_transition(read1, character="g")
    trap1.add_transition(trap1, character="c")

    pop4.add_transition(accept5, character="$")

    start_state = DPDA.State(state_type="Start", next_state=read1)

    my_pda = DPDA.PDA(start_state)

    tape_word = "aaaabbbbaaaabbbb$"
    my_pda.start(tape=tape_word, stack=['$'])

    tape_word = "$"
    my_pda.start(tape=tape_word, stack=['$'])

    tape_word = "ababababababab$"
    my_pda.start(tape=tape_word, stack=['$'])

    tape_word = "abbabbacgb$"
    my_pda.start(tape=tape_word, stack=['$'])

    tape_word = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaac$"
    my_pda.start(tape=tape_word, stack=['$'])

    tape_word = "g$"
    my_pda.start(tape=tape_word, stack=['$'])




if __name__ == "__main__":
    main()
