#!/bin/bash

# 指定你要检查的目录
root_dir="./Result"

# 使用find命令递归地查找所有的文件
# -type f参数表示只查找文件，而不是目录
# -empty参数表示只查找空文件
empty_files=$(find "$root_dir" -type f -empty)

# 如果找到了空文件，就输出它们的相对路径和名字
if [ -n "$empty_files" ]; then
    echo "Found empty files:"
    
    # 将 IFS 设置为换行符，这样就能正确处理包含空格的文件名了
    IFS=$'\n'
    for file in $empty_files; do
        # 使用realpath命令将文件的绝对路径转换为相对于root_dir的相对路径
        relative_path=$(realpath --relative-to="$root_dir" "$file")
        echo "$relative_path"
    done
    # 将 IFS 恢复为默认值
    IFS=$' \t\n'
else
    echo "No empty files found."
fi
