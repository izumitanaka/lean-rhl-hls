#!/usr/bin/env python3
"""External RTL checks for fixed-region entry boundary cases."""
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'artifacts/fixed-generation'


def bench(arrays, registers, expected_arrays, expected_registers, invalid_reads):
    lines = ['''module tb;
reg clk=0; always #5 clk=~clk;
reg rst=1,start=0,cfg_we=0,cfg_reg=0,read_reg=0;
reg [31:0] x=0,y=0,cfg_id=0,cfg_addr=0,cfg_data=0,read_id=0,read_addr=0;
wire [31:0] read_data; wire read_valid,busy,done,error; integer cycles;
hls_top dut(.*);
initial begin
repeat (2) @(negedge clk); rst=0;
repeat (2) begin
''']
    for bank, values in arrays.items():
        for index, value in enumerate(values):
            lines.append(f'@(negedge clk); cfg_we=1; cfg_reg=0; cfg_id={bank}; cfg_addr={index}; cfg_data={value}; @(negedge clk); cfg_we=0;')
    for reg, value in registers.items():
        lines.append(f'@(negedge clk); cfg_we=1; cfg_reg=1; cfg_id={reg}; cfg_data={value}; @(negedge clk); cfg_we=0;')
    lines.append('''@(negedge clk); start=1; @(negedge clk); start=0; cycles=0;
while (!done && cycles<1000) begin @(negedge clk); cycles=cycles+1; end
if (!done || busy || error) $fatal(1,"execution failed");''')
    for bank, values in expected_arrays.items():
        for index, value in enumerate(values):
            lines.append(f'read_reg=0; read_id={bank}; read_addr={index}; #1; if (!read_valid || read_data !== 32\'d{value}) $fatal(1,"array {bank}[{index}]");')
    for reg, value in expected_registers.items():
        lines.append(f'read_reg=1; read_id={reg}; #1; if (!read_valid || read_data !== 32\'d{value}) $fatal(1,"register {reg}");')
    for bank, index in invalid_reads:
        lines.append(f'read_reg=0; read_id={bank}; read_addr={index}; #1; if (read_valid !== 1\'b0) $fatal(1,"unexpected valid array element");')
    lines.append('end $display("PASS external RTL"); $finish; end\ninitial begin #200000; $fatal(1,"timeout"); end\nendmodule\n')
    return '\n'.join(lines)


def main():
    data = [10,20,30,40]
    cases = [
        ('sparse', {7:data,11:[0]*4}, {}, {7:data,11:data}, {}, [(11,4)]),
        ('scalar', {}, {}, {}, {0:42}, [(0,0)]),
        ('empty', {}, {}, {}, {}, [(7,0)]),
        ('captured', {}, {0:17,1:0}, {}, {0:18,1:17}, [(0,0)]),
        ('captured-loop', {}, {0:17,1:0}, {}, {0:20,1:54}, [(0,0)]),
        ('captured-overflow', {}, {0:4294967295,1:0}, {}, {0:0,1:4294967295}, [(0,0)]),
        ('captured-loop-overflow', {}, {0:4294967295,1:0}, {}, {0:2,1:0}, [(0,0)]),
    ]
    records = []
    with tempfile.TemporaryDirectory(prefix='fixed-generation-') as tmp:
        for name, *args in cases:
            tb = OUT / f'{name}-tb.sv'
            tb.write_text(bench(*args))
            exe = Path(tmp) / name
            for phase, command in [
                ('compile', ['iverilog','-g2012','-s','tb','-o',str(exe),str(OUT / f'{name}.sv'),str(tb)]),
                ('simulation', ['vvp',str(exe)]),
            ]:
                result = subprocess.run(command,text=True,capture_output=True,timeout=60)
                (OUT / f'{name}-{phase}.log').write_text(result.stdout+result.stderr)
                if result.returncode:
                    raise RuntimeError(f'{name}/{phase}: {result.stdout}{result.stderr}')
            if 'PASS external RTL' not in result.stdout:
                raise RuntimeError(f'{name}: success marker missing')
            records.append({'case':name,'status':'pass','invocations':2})
            print(f'PASS {name}')
    (OUT / 'simulation.json').write_text(json.dumps(
        {'tool':'iverilog/vvp','synthesis_run':False,'cases':records},indent=2)+'\n')


if __name__ == '__main__':
    main()
