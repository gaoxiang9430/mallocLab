from socket import *
import sys 
import os
import struct

if(len(sys.argv)<3):
	print "please exectute this file: \"./client.py [your team id] [your password]\""
	exit()
	
ADDR = ('211.87.235.74',8000)
BUFSIZE = 1024
filename = 'src/mm.c'

FILEINFO_SIZE=struct.calcsize('128s32sI8s')
sendSock = socket(AF_INET,SOCK_STREAM)
sendSock.connect(ADDR)


sendSock.send(str(len(sys.argv[1])))
sendSock.send(sys.argv[1])
sendSock.send(str(len(sys.argv[2])))
sendSock.send(sys.argv[2])

fhead=struct.pack('128s11I',filename,0,0,0,0,0,0,0,0,os.stat(filename).st_size,0,0)
sendSock.send(fhead)

fp = open(filename,'rb')

while 1:

    filedata = fp.read(BUFSIZE)

    if not filedata: break

    sendSock.send(filedata)

print "waiting for result..."


fhead = sendSock.recv(FILEINFO_SIZE)	
filename,temp1,filesize,temp2=struct.unpack('128s32sI8s',fhead)
restsize = filesize
print "your result :\n"
while 1:    #read file data 
		if restsize > BUFSIZE:
		    filedata = sendSock.recv(BUFSIZE)
		else:
		    filedata = sendSock.recv(restsize)

		if not filedata: break
		print filedata
		restsize = restsize-len(filedata)
		if restsize == 0:
			break
len_name = sendSock.recv(1)
bestResult=sendSock.recv(int(len_name))
print "The Best Result Till Now: ",bestResult
fp.close()

sendSock.close()
