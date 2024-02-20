import networkx as nx
import tkinter as tk
from tkinter import filedialog

def state_elimination(mode= False, test = ""):
    G = nx.DiGraph()
    i = 0
    if mode == False:
        num_nodes = int(input("Введите количество узлов: "))
        nodes = [input(f"Введите название узла {i + 1}: ") for i in range(num_nodes)]
        G.add_nodes_from(nodes)

        num_edges = int(input("Введите количество ребер: "))
        print("Введите ребра в формате 'начальный_узел конечный_узел метка_ребра', например 'Q Q1 a'")
        for _ in range(num_edges):
            edge = input("Введите ребро: ").split()
            G.add_edge(edge[0], edge[1], label=edge[2])
    else:
        if test != "":
            file_path = test
        else:
            file_path = filedialog.askopenfilename()
        if file_path:
            with open(file_path, 'r') as file:
                lines = file.read().splitlines()
                for line in lines:
                    parts = line.split()
                    if i == 0:
                        G.add_nodes_from(parts)
                        nodes = parts
                        i += 1
                    else:
                        G.add_edge(parts[0], parts[3], label=parts[1])

    new_start = str(nodes[0][0]) + "0"
    G.add_node(new_start)
    for node in G.nodes():
        if G.in_degree(node) == 0 and node != new_start:
            G.add_edge(new_start, node, label="eps")

    new_final = str(nodes[0][0]) + "f"
    G.add_node(new_final)
    for node in G.nodes():
        if G.out_degree(node) == 0 and node != new_final:
            G.add_edge(node, new_final, label="eps")

    for node in G.nodes():
        if node in [new_start, new_final]:
            continue
        for pred in G.predecessors(node):
            for succ in G.successors(node):
                if pred == succ:
                    continue
                pred_succ_label = G[pred][node]["label"] + G[node][succ]["label"]
                if G.has_edge(pred, succ):
                    G[pred][succ]["label"] = "(" + G[pred][succ]["label"] + "|" + pred_succ_label + ")*"
                else:
                    G.add_edge(pred, succ, label=pred_succ_label)
        G = G.copy()
        G.remove_node(node)

    return pred_succ_label