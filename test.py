import subprocess
import os

if __name__ == "__main__":
    resPath='./result'
    if not os.path.exists(resPath):
        os.makedirs(resPath)
    benchPath='./Benchmark/PLDI'
    for dirPath,dirNames,fileNames in os.walk(benchPath):
        for file in fileNames:
            relPath=os.path.relpath(dirPath,benchPath)
            newPath=os.path.join(resPath,relPath)
            newFilePath=os.path.join(newPath,file.replace(".c",".out"))
            if not os.path.exists(newPath):
                os.makedirs(newPath)
            command=f"./bin/Inv sv {os.path.join(dirPath,file)}"
            result=subprocess.run(command, shell=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
            with open(newFilePath,'w',encoding='utf-8') as f:
                f.write(result.stdout.decode('utf-8'))
                f.write(result.stderr.decode('utf-8'))
            