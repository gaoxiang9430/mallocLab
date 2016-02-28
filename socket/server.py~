from socket import *
import struct
import thread
import os

ADDR = ('127.0.0.1',8080)

BUFSIZE = 1024
FILEINFO_SIZE=struct.calcsize('128s32sI8s')
recvSock = socket(AF_INET,SOCK_STREAM)
recvSock.bind(ADDR)
recvSock.listen(True)

filename="huahua_mm.c"
import subprocess
var = "/usr/bin/perl"
subprocess.call(["perl", "grade-malloclab.pl",'-f', filename,var])
print "hahaha"
def test(name,passwd):
	sourceFile=open("passwd.txt","r")
	while True:
		line = sourceFile.readline()
		if not line:
			break
		dataArray = line.split()
		if(dataArray[0]==name and dataArray[1]==passwd):
			return 1
	return 0

def readDate(conn):

	len_name = conn.recv(1)
	name=conn.recv(int(len_name))
	len_name = conn.recv(1)
	passwd=conn.recv(int(len_name))
	print name, passwd
	
	isvalid = test(name,passwd)
	if(isvalid==0):
		conn.send("incorrect name or password")
		conn.close()
		return
		
	fhead = conn.recv(FILEINFO_SIZE)
	
	filename,temp1,filesize,temp2=struct.unpack('128s32sI8s',fhead)

	filename = name+"_mm.c"    #recieved file
	fp = open(filename,'wb')

	restsize = filesize

	while 1:    #read file data 
		if restsize > BUFSIZE:
		    filedata = conn.recv(BUFSIZE)
		else:
		    filedata = conn.recv(restsize)

		if not filedata: break
		fp.write(filedata)
		restsize = restsize-len(filedata)
		if restsize == 0:
			break
	print "recieve completed ..."

	import subprocess
	var = "/usr/bin/perl"
	subprocess.call(["perl", "grade-malloclab.pl",'-f', filename,var])
	print "I am running"
	#conn.sendData(conn)
	fp.close()
	conn.close()

while(True):   # waiting to connect
	conn,addr = recvSock.accept()
	thread.start_new_thread(readDate,(conn))
	
	#print "close..."

recvSock.close()
