mkdir  -p  'Nid'
for  x  in *.c;  do  
time_start=$(($(date +%s%N)/1000000))
/usr/bin/clang-3.8 -emit-llvm -S -o "Nid/${x%.c}.ll" $x
time_end=$(($(date +%s%N)/1000000))
let time_total=time_end-time_start
echo "Total time in milliseconds:"
echo $time_total
done
