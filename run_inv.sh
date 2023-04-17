#!/bin/bash

# 定义文件夹路径
root_path="."
benchmark_path="$root_path/Benchmark"
result_path="$root_path/Result"

# 检查 Inv 二进制文件是否存在
if [ ! -f "$root_path/Inv" ]; then
  echo "Inv 二进制文件不存在"
  exit 1
fi

# 遍历 Benchmark 文件夹下的子文件夹
for folder in "$benchmark_path"/*; do
  if [ -d "$folder" ]; then
    folder_name=$(basename "$folder")
    result_folder="$result_path/$folder_name"

    # 创建 Result 文件夹下的同名文件夹
    mkdir -p "$result_folder"

    # 遍历子文件夹内的 .c 文件
    for c_file in "$folder"/*.c; do
      if [ -f "$c_file" ]; then
        file_name=$(basename "$c_file" .c)
        output_file="$result_folder/$file_name.cfg"

        # 使用 Inv 执行 .c 文件并将结果导出到 .cfg 文件
        $root_path/Inv "$c_file" > "$output_file"
      fi
    done
  fi
done
