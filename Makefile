
bin/Debug/mcBV.exe: *.fs
	xbuild /p:Configuration=Debug mcBV-mono.fsproj

bin/Release/mcBV.exe: *.fs
	xbuild /p:Configuration=Release mcBV-mono.fsproj

debug: bin/Debug/mcBV.exe

release: bin/Release/mcBV.exe

all: debug release 

clean:
	rm -rf bin/Debug
	rm -rf bin/Release
