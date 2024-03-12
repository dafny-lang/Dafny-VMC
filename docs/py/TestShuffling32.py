import DafnyVMC

def main():
    arr1 = [0, 1, 2]
    arr2 = [float(0), float(1), float(2)]
    arr3 = ["aa", "bb", "cc"]
    arr4 = ['a', 'b', 'c']
    arr5 = [True, False, False, True]

    # STANDARD RNG
    print("\nSTANDARD RNG TESTS WITH CUSTOM UNIFORM\n")
        
    r = DafnyVMC.Random()

    print("Example of Fisher-Yates: int")
    arr1 = r.Shuffle32(arr1)
    print(arr1)

    print("Example of Fisher-Yates: float")
    arr2 = r.Shuffle32(arr2)
    print(arr2)

    print("Example of Fisher-Yates: str")
    arr3 = r.Shuffle32(arr3)
    print(arr3)

    print("Example of Fisher-Yates: char/str")
    arr4 = r.Shuffle32(arr4)
    print(arr4)

    print("Example of Fisher-Yates: boolean")
    arr5 = r.Shuffle32(arr5)
    print(arr5)

if __name__ == "__main__":
    main()