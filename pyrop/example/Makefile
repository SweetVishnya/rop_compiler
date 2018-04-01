default:
	gcc -g -fno-stack-protector bof.c -o bof -masm=intel
	gcc -g -fno-stack-protector bof_syscall.c -o bof_syscall -masm=intel
	gcc -g -fno-stack-protector bof_system.c -o bof_system -masm=intel
	gcc -g -fno-stack-protector bof_shell.c -o bof_shell -masm=intel
	gcc -g -fno-stack-protector bof_read_got.c -o bof_read_got -masm=intel

strcpy:
	clang -g -fno-stack-protector strcpy.c -o strcpy -masm=intel -ldl -m32

gets:
	gcc -g -fno-stack-protector gets.c -o gets -masm=intel

arm:
	arm-linux-gnueabi-gcc -fno-stack-protector arm_bof.c -o arm_bof --static

clean:
	rm bof
