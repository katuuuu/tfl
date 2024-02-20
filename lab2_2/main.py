import FSM

def test(file_path, number):
    regex = FSM.state_elimination(True, file_path)
    with open("result\\result_" + str(number) + ".txt" , "w") as f:
        f.write(regex)
def main():
    list_path = ["test\\test_1.txt","test\\test_2.txt","test\\test_3.txt","test\\test_4.txt","test\\test_5.txt",
                 "test\\test_6.txt", "test\\test_7.txt","test\\test_8.txt","test\\test_9.txt", "test\\test_10.txt"]
    number = 1
    for file_path in list_path:
        test(file_path, number)
        number += 1

if __name__ == "__main__":
    main()