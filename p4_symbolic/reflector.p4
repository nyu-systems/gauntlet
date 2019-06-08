/* -*- P4_16 -*- */
#include <core.p4>
#include <v1model.p4>

/*************************************************************************
*********************** H E A D E R S  ***********************************
*************************************************************************/

typedef bit<48> macAddr_t;

header eth_t {
    macAddr_t dst;
    macAddr_t src;
    bit<16>   etherType;
}

struct metadata {
    /* empty */
}

struct headers {
    eth_t   eth;
}

/*************************************************************************
*********************** P A R S E R  ***********************************
*************************************************************************/

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {

      state start{
      packet.extract(hdr.eth);
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

control MyIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {

    action bounce(){
       // Swap MAC addresses.
       macAddr_t tmp;
       tmp = hdr.eth.src;
       hdr.eth.src = hdr.eth.dst;
       hdr.eth.dst = tmp;
       //Set Output port == Input port
       standard_metadata.egress_spec = standard_metadata.ingress_port;
    }

    action drop() {
      mark_to_drop();
    }

    table mac_check {
        key = {
            hdr.eth.src: exact;
        }
        actions = {
            drop;
            bounce;
        }
        size = 1024;
        default_action = drop();
    }

    apply {
        if (hdr.eth.isValid()){
            mac_check.apply();
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
    apply { }
}

/*************************************************************************
***********************  D E P A R S E R  *******************************
*************************************************************************/

control MyDeparser(packet_out packet, in headers hdr) {
    apply {
        // parsed headers have to be added again into the packet
        packet.emit(hdr.eth);
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
