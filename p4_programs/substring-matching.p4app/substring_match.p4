/*
Copyright 2019 Contributors of the p4 hackathon (https://github.com/pl-ca/p4hackathon)

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

/* -*- P4_16 -*- */
#include <core.p4>
#include <v1model.p4>

/*************************************************************************
*********************** H E A D E R S  ***********************************
*************************************************************************/

typedef bit<64> string_t;

typedef bit<9>  egressSpec_t;

header hdrtype_t {
    bit<8> input_or_internal;
}
header input_t {
    string_t strA;
    string_t strB;
}
header output_t {
    bit<8> highest_count;
    string_t result;
}

header internal_t {
    bit<32> iterator_l;
    bit<32> iterator_r;
    bit<32> highest_count;
    string_t matrix_l0;
    string_t matrix_l1;
    string_t matrix_l2;
    string_t matrix_l3;
    string_t matrix_l4;
    string_t matrix_l5;
    string_t matrix_l6;
    string_t matrix_l7;
}

struct metadata {
    /* empty */
    bit<8>  charA;
    bit<8>  charB;
}

struct headers {
    hdrtype_t  type_header;
    output_t output_header;
    internal_t internal_header;
    input_t    input_header;
}

/*************************************************************************
*********************** P A R S E R  ***********************************
*************************************************************************/

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {

    state start {
        packet.extract(hdr.type_header);        
        transition select(hdr.type_header.input_or_internal) {
            0: parse_input;
            1: parse_internal;
            default: parse_output;
        }
    }

    state parse_output {
        packet.extract(hdr.output_header);
        transition parse_input;
    }
    state parse_internal {
        packet.extract(hdr.internal_header);
        transition parse_input;
    }

    state parse_input {
        packet.extract(hdr.input_header);
        transition accept;
    }

    state parse_reject {
        transition accept;
    }

}

/*************************************************************************
************   C H E C K S U M    V E R I F I C A T I O N   *************
*************************************************************************/

control MyVerifyChecksum(inout headers hdr, inout metadata meta) {   
    apply {  }
}


/*************************************************************************
**************  I N G R E S S   P R O C E S S I N G   *******************
*************************************************************************/

control IncrementCount(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata)
{
    bit<3> diagonal_index_in_bytes = 0;
    bit<8> diagonal_index_in_bits = 0;
    bit<8> temp_count = 0;
    bit<64> temp_value = 0;
    action set_l0_count(string_t val)
    {
        hdr.internal_header.matrix_l0 = hdr.internal_header.matrix_l0 | val;
    }
    action set_l1_first()
    {
        hdr.internal_header.matrix_l1 = hdr.internal_header.matrix_l1 | 1;
    }
    action set_l2_first()
    {
        hdr.internal_header.matrix_l2 = hdr.internal_header.matrix_l2 | 1;
    }
    action set_l3_first()
    {
        hdr.internal_header.matrix_l3 = hdr.internal_header.matrix_l3 | 1;
    }
    action set_l4_first()
    {
        hdr.internal_header.matrix_l4 = hdr.internal_header.matrix_l4 | 1;
    }
    action set_l5_first()
    {
        hdr.internal_header.matrix_l5 = hdr.internal_header.matrix_l5 | 1;
    }
    action set_l6_first()
    {
        hdr.internal_header.matrix_l6 = hdr.internal_header.matrix_l6 | 1;
    }
    action set_l7_first()
    {
        hdr.internal_header.matrix_l7 = hdr.internal_header.matrix_l7 | 1;
    }
    action increment_l1_count()
    {
        diagonal_index_in_bytes = (bit<3>) hdr.internal_header.iterator_r; // get the current line index
        diagonal_index_in_bytes = diagonal_index_in_bytes + 7;             // get the corresponding diagonal index from last line
        diagonal_index_in_bits = (bit<8>) diagonal_index_in_bytes << 3;    // multiply by 8 to shift in bytes resolution
        temp_count = ((bit<8>) (hdr.internal_header.matrix_l0 >> diagonal_index_in_bits) & 0xff) + 1; // compute the new value to write in the matrix

        diagonal_index_in_bits =  (bit<8>)hdr.internal_header.iterator_r << 3; // calculate where to put the resulting count in the matrix line
        temp_value = ((bit<64>) temp_count) << diagonal_index_in_bits; // calculate the value over 64b

        hdr.internal_header.matrix_l1 = temp_value | hdr.internal_header.matrix_l1;
    }
    action increment_l2_count()
    {
        diagonal_index_in_bytes = (bit<3>) hdr.internal_header.iterator_r; // get the current line index
        diagonal_index_in_bytes = diagonal_index_in_bytes + 7;             // get the corresponding diagonal index from last line
        diagonal_index_in_bits = (bit<8>) diagonal_index_in_bytes << 3;    // multiply by 8 to shift in bytes resolution
        temp_count = ((bit<8>) (hdr.internal_header.matrix_l1 >> diagonal_index_in_bits) & 0xff) + 1; // compute the new value to write in the matrix

        diagonal_index_in_bits =  (bit<8>)hdr.internal_header.iterator_r << 3; // calculate where to put the resulting count in the matrix line
        temp_value = ((bit<64>) temp_count) << diagonal_index_in_bits; // calculate the value over 64b

        hdr.internal_header.matrix_l2 = temp_value | hdr.internal_header.matrix_l2;
    }

    action increment_l3_count()
    {
        diagonal_index_in_bytes = (bit<3>) hdr.internal_header.iterator_r; // get the current line index
        diagonal_index_in_bytes = diagonal_index_in_bytes + 7;             // get the corresponding diagonal index from last line
        diagonal_index_in_bits = (bit<8>) diagonal_index_in_bytes << 3;    // multiply by 8 to shift in bytes resolution
        temp_count = ((bit<8>) (hdr.internal_header.matrix_l2 >> diagonal_index_in_bits) & 0xff) + 1; // compute the new value to write in the matrix

        diagonal_index_in_bits =  (bit<8>)hdr.internal_header.iterator_r << 3; // calculate where to put the resulting count in the matrix line
        temp_value = ((bit<64>) temp_count) << diagonal_index_in_bits; // calculate the value over 64b

        hdr.internal_header.matrix_l3 = temp_value | hdr.internal_header.matrix_l3;
    }
    action increment_l4_count()
    {
        diagonal_index_in_bytes = (bit<3>) hdr.internal_header.iterator_r; // get the current line index
        diagonal_index_in_bytes = diagonal_index_in_bytes + 7;             // get the corresponding diagonal index from last line
        diagonal_index_in_bits = (bit<8>) diagonal_index_in_bytes << 3;    // multiply by 8 to shift in bytes resolution
        temp_count = ((bit<8>) (hdr.internal_header.matrix_l3 >> diagonal_index_in_bits) & 0xff) + 1; // compute the new value to write in the matrix

        diagonal_index_in_bits =  (bit<8>)hdr.internal_header.iterator_r << 3; // calculate where to put the resulting count in the matrix line
        temp_value = ((bit<64>) temp_count) << diagonal_index_in_bits; // calculate the value over 64b

        hdr.internal_header.matrix_l4 = temp_value | hdr.internal_header.matrix_l4;
    }

    action increment_l5_count()
    {
        diagonal_index_in_bytes = (bit<3>) hdr.internal_header.iterator_r; // get the current line index
        diagonal_index_in_bytes = diagonal_index_in_bytes + 7;             // get the corresponding diagonal index from last line
        diagonal_index_in_bits = (bit<8>) diagonal_index_in_bytes << 3;    // multiply by 8 to shift in bytes resolution
        temp_count = ((bit<8>) (hdr.internal_header.matrix_l4 >> diagonal_index_in_bits) & 0xff) + 1; // compute the new value to write in the matrix

        diagonal_index_in_bits =  (bit<8>)hdr.internal_header.iterator_r << 3; // calculate where to put the resulting count in the matrix line
        temp_value = ((bit<64>) temp_count) << diagonal_index_in_bits; // calculate the value over 64b

        hdr.internal_header.matrix_l5 = temp_value | hdr.internal_header.matrix_l5;
    }
    action increment_l6_count()
    {
        diagonal_index_in_bytes = (bit<3>) hdr.internal_header.iterator_r; // get the current line index
        diagonal_index_in_bytes = diagonal_index_in_bytes + 7;             // get the corresponding diagonal index from last line
        diagonal_index_in_bits = (bit<8>) diagonal_index_in_bytes << 3;    // multiply by 8 to shift in bytes resolution
        temp_count = ((bit<8>) (hdr.internal_header.matrix_l5 >> diagonal_index_in_bits) & 0xff) + 1; // compute the new value to write in the matrix

        diagonal_index_in_bits =  (bit<8>)hdr.internal_header.iterator_r << 3; // calculate where to put the resulting count in the matrix line
        temp_value = ((bit<64>) temp_count) << diagonal_index_in_bits; // calculate the value over 64b

        hdr.internal_header.matrix_l6 = temp_value | hdr.internal_header.matrix_l6;
    }
    action increment_l7_count()
    {
        diagonal_index_in_bytes = (bit<3>) hdr.internal_header.iterator_r; // get the current line index
        diagonal_index_in_bytes = diagonal_index_in_bytes + 7;             // get the corresponding diagonal index from last line
        diagonal_index_in_bits = (bit<8>) diagonal_index_in_bytes << 3;    // multiply by 8 to shift in bytes resolution
        temp_count = ((bit<8>) (hdr.internal_header.matrix_l6 >> diagonal_index_in_bits) & 0xff) + 1; // compute the new value to write in the matrix

        diagonal_index_in_bits =  (bit<8>)hdr.internal_header.iterator_r << 3; // calculate where to put the resulting count in the matrix line
        temp_value = ((bit<64>) temp_count) << diagonal_index_in_bits; // calculate the value over 64b

        hdr.internal_header.matrix_l7 = temp_value | hdr.internal_header.matrix_l7;
    }
    table increment_count
    {
        key = 
        {
            hdr.internal_header.iterator_l: ternary;
            hdr.internal_header.iterator_r: ternary;
        }
        actions = 
        {
            set_l0_count;
            set_l1_first;
            set_l2_first;
            set_l3_first;
            set_l4_first;
            set_l5_first;
            set_l6_first;
            set_l7_first;
            increment_l1_count;
            increment_l2_count;
            increment_l3_count;
            increment_l4_count;
            increment_l5_count;
            increment_l6_count;
            increment_l7_count;
            NoAction;
        }
        default_action = NoAction();
    }

    apply {
        if (increment_count.apply().hit)
        {
            if ((bit<32>) temp_count > hdr.internal_header.highest_count)
            {
                hdr.internal_header.highest_count = (bit<32>) temp_count;
            }
        }
    }
}
control MyIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {

    action get_strA_char0(){
        meta.charA = hdr.input_header.strA[63:56];
    }

    action get_strA_char1(){
        meta.charA = hdr.input_header.strA[55:48];
    }

    action get_strA_char2(){
        meta.charA = hdr.input_header.strA[47:40];
    }

    action get_strA_char3(){
       meta.charA = hdr.input_header.strA[39:32];
    }

    action get_strA_char4(){
        meta.charA = hdr.input_header.strA[31:24];
    }

    action get_strA_char5(){
        meta.charA = hdr.input_header.strA[23:16];
    }

    action get_strA_char6(){
        meta.charA = hdr.input_header.strA[15:8];
    }

    action get_strA_char7(){
       meta.charA = hdr.input_header.strA[7:0];
    }

    action get_strB_char0(){
        meta.charB = hdr.input_header.strB[63:56];
    }

    action get_strB_char1(){
        meta.charB = hdr.input_header.strB[55:48];
    }

    action get_strB_char2(){
        meta.charB = hdr.input_header.strB[47:40];
    }

    action get_strB_char3(){
        meta.charB = hdr.input_header.strB[39:32];
    }

    action get_strB_char4(){
        meta.charB = hdr.input_header.strB[31:24];
    }

    action get_strB_char5(){
        meta.charB = hdr.input_header.strB[23:16];
    }

    action get_strB_char6(){
        meta.charB = hdr.input_header.strB[15:8];
    }

    action get_strB_char7(){
        meta.charB = hdr.input_header.strB[7:0];
    }

    table get_strA_char{
        key = {
            hdr.internal_header.iterator_r : exact;
        }
        actions = {
            get_strA_char0;
            get_strA_char1;
            get_strA_char2;
            get_strA_char3;
            get_strA_char4;
            get_strA_char5;
            get_strA_char6;
            get_strA_char7;
        }
    }

    table get_strB_char{
        key = {
            hdr.internal_header.iterator_l: exact;
        }
        actions = {
            get_strB_char0;
            get_strB_char1;
            get_strB_char2;
            get_strB_char3;
            get_strB_char4;
            get_strB_char5;
            get_strB_char6;
            get_strB_char7;
        }
    }


    action do_recirculate(){
        recirculate(meta);
    }
    action do_output(){
        standard_metadata.egress_spec = 1;
        // mark_to_drop();        
    }

    action convert_to_output(){
        hdr.output_header.setValid();
        hdr.output_header.highest_count = (bit<8>) hdr.internal_header.highest_count;
        hdr.internal_header.setInvalid();
        hdr.type_header.input_or_internal = 0;
        do_output();
    }

     action update_indices (){
        hdr.internal_header.iterator_r = hdr.internal_header.iterator_r + 1;
        if(hdr.internal_header.iterator_r == 8){
            hdr.internal_header.iterator_r = 0;
            hdr.internal_header.iterator_l = hdr.internal_header.iterator_l + 1;
        }
        if (hdr.internal_header.iterator_l < 8){
            do_recirculate();
        } else {
            convert_to_output();
        }
    }
 
    action convert_to_internal(){
        hdr.internal_header.setValid();
        hdr.internal_header.iterator_l = 0;
        hdr.internal_header.iterator_r = 0;
        hdr.internal_header.highest_count = 0;
        hdr.internal_header.matrix_l0 = 0;
        hdr.internal_header.matrix_l1 = 0;
        hdr.internal_header.matrix_l2 = 0;
        hdr.internal_header.matrix_l3 = 0;
        hdr.internal_header.matrix_l4 = 0;
        hdr.internal_header.matrix_l5 = 0;
        hdr.internal_header.matrix_l6 = 0;
        hdr.internal_header.matrix_l7 = 0;
        hdr.type_header.input_or_internal = 1;

        do_recirculate();
    }

 
    table test {
        key = {
            hdr.internal_header.iterator_r : exact;
            hdr.internal_header.iterator_l : exact;
        }
        actions = { NoAction; }
        default_action = NoAction;
    }
 
    apply {

        if(hdr.type_header.input_or_internal == 0){
           convert_to_internal();
        } else {
            // probably not needed
            hdr.internal_header.setValid();

            get_strA_char.apply();
            get_strB_char.apply();
            
            if (meta.charA == meta.charB)
            {
                IncrementCount.apply(hdr, meta, standard_metadata);
            }
            // test.apply();

            hdr.internal_header.iterator_r = hdr.internal_header.iterator_r + 1;
            if(hdr.internal_header.iterator_r == 8){
                hdr.internal_header.iterator_r = 0;
                hdr.internal_header.iterator_l = hdr.internal_header.iterator_l + 1;
            }
            if (hdr.internal_header.iterator_l < 8){
                do_recirculate();
            } else {
                convert_to_output();
            }
        }
    }
}


/*************************************************************************
****************  E G R E S S   P R O C E S S I N G   *******************
*************************************************************************/

control MyEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply {  }
}

/*************************************************************************
*************   C H E C K S U M    C O M P U T A T I O N   **************
*************************************************************************/

control MyComputeChecksum(inout headers  hdr, inout metadata meta) {
     apply {
    }
}

/*************************************************************************
***********************  D E P A R S E R  *******************************
*************************************************************************/

control MyDeparser(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.type_header);
        packet.emit(hdr.output_header);
        packet.emit(hdr.internal_header);
        packet.emit(hdr.input_header);
    }
}

/*************************************************************************
***********************  S W I T C H  *******************************
*************************************************************************/

V1Switch(
MyParser(),
MyVerifyChecksum(),
MyIngress(),
MyEgress(),
MyComputeChecksum(),
MyDeparser()
) main;
