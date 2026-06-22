zig build install

if [ $? -ne 0 ]; then 
	echo "zig build failed";
	exit 1; 
fi

echo "SM-PDS:"
./zig-out/bin/bcaret_mc_smpds --pytest tests/performance.json

echo "Naive:"
./zig-out/bin/bcaret_mc_smpds --pytest --naive tests/performance.json

