from PDA import *
from random import randint

class State(object):
    def __init__(self, state_type, next_state=None):
        if state_type not in ('Accept', 'Push', 'Pop', 'Read', 'Start', 'Trap'):
            raise SystemExit(state_type + " is not a valid State type!")
        if state_type == 'Start' and not next_state:
            raise SystemExit("Start states must be provided a next_state!")
        self.state_type = state_type
        self.transitions = list()
        self.next_state = next_state
        self.number = len(state_type) * 2

    def add_transition(self, next_state, character=None):
        transition = {'char': character, 'next': next_state}
        self.transitions.append(transition)



    def get_next_state(self, character=None):
        if self.state_type == "Start":
            return self.next_state

        if self.state_type == "Read":
            if character == "":
                return self.transitions[0]['next']

            for transition in self.transitions:
                if transition['char'] == character:
                    return transition['next']

        if self.state_type == "Push":
            return self.transitions[0]['next']

        if self.state_type == "Pop":
            for transition in self.transitions:
                if transition['char'] == character:
                    return transition['next']
        if self.state_type == "Trap":
            epsilon_states = []
            for transition in self.transitions:
                if transition['char'] is None:
                    epsilon_states.append(transition['next'])
            return epsilon_states

    def action(self, tape, stack,step = 0, current_state="first",rule_num=0, verbose=True):
        with open("test\\test.dat" , "a") as f:
            if verbose:
                if current_state == "first":
                    print("Step#    State Rule  Stack        Input Left")
                    print("0    q_0    0    ----         TAPE:  " + tape)
                    f.write("Step#    State Rule  Stack        Input Left\n")
                    f.write("0    q_0    0    ----         TAPE:  " + tape + "\n")
                if current_state == "q-2":
                    if tape[0] == "b":
                        rule_num = 4
                        current_state = "q-2"
                    else:
                        current_state = "q-3"
                        rule_num = 5
                elif current_state == "q-1":
                    if tape[0] == "a":
                        rule_num = 2
                        current_state = "q-1"
                    elif tape[0] == "b":
                        rule_num = 3
                        current_state = "q-2"
                elif current_state == "q-0":
                    current_state = "q-1"
                    rule_num = 1
                if current_state != "first":
                    if step < 10:
                        print(step, end="    ")
                    else:
                        print(step, end="   ")
                    print(current_state, end="    ")
                    print(rule_num, end="    ")
                    if stack:
                        print("STACK: ", stack[-1], end="    ")
                    else:
                        print("STACK: ", stack, end="    ")
                    print("TAPE: ", tape)
                    f.write(str(step) + "    " + current_state + "    " + str(rule_num) + "    ")
                    if stack:
                        f.write("STACK: " + str(stack[-1]) + "    ")
                    else:
                        f.write("STACK: " + str(stack) + "    ")
                    f.write("TAPE: " + tape + "\n")
        try:
            if self.state_type == "Start":
                current_state="q-0"
                rule_num=0
                self.get_next_state().action(tape, stack, step+1,current_state,rule_num,
                                             verbose)
            elif self.state_type == "Read":
                self.get_next_state(character=tape[0]).action(tape[1:], stack, step+1,
                                                              current_state,rule_num,
                                                              verbose)
            elif self.state_type == "Push":
                char = self.transitions[0]['char']
                stack.append(char)
                self.get_next_state().action(tape, stack, step+1,current_state,
                                             rule_num, verbose)
            elif self.state_type == "Pop":
                char = stack.pop()
                self.get_next_state(character=char).action(tape, stack, step+1,
                                                           current_state,rule_num, verbose)
            elif self.state_type == "Accept":
                print("Tape accepted!")
                if verbose:
                    print("FINAL TAPE: ", tape)
                    print("FINAL STACK: ", stack)
            elif self.state_type == "Trap":
                char = stack.pop()
                next_states = self.get_next_state().action(tape, stack, step+1,current_state,
                                             rule_num, verbose)
                for state in next_states:
                    state.action(tape, stack, step + 1, current_state, rule_num, verbose)
            else:
                pass
        except:
            print("Tape NOT accepted!")
            if verbose:
                print("FINAL TAPE: ", tape)
                print("FINAL STACK: ", stack)