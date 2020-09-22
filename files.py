import csv

lines = [
    ["pepe", "garcia"],
    ["dani", "garcia"]
]

with open("/home/pepe/file.csv", "w") as file:
    writer = csv.writer(file)

    for line in lines:
        writer.writerow(line)


with open("/home/pepe/file.csv") as file:
    reader = csv.reader(file)

    for line in reader:

        print(line)
