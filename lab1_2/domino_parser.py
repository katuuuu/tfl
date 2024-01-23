def parse_dominos(file_path):
    dominos = []
    with open(file_path, 'r') as file:
        for line in file:
            parts = line.strip().split(',')
            if len(parts) == 2:
                dominos.append((parts[0].strip('() '), parts[1].strip('() ')))
    return dominos
