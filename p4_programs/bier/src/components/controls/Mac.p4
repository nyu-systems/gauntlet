/* Mac.p4 -*- c -*-
 * 
 * This control unit applies layer 2 address manipulation 
 *
 */
control Mac(inout headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {


	/*
	* Set layer 2 mac srcAddr and dstAddr
	*/
	action set_mac(macAddr_t srcAddr, macAddr_t dstAddr) {
		hdr.ethernet.srcAddr = srcAddr;
		hdr.ethernet.dstAddr = dstAddr;
	}

	/*
	* Helper table to trigger mac manipulation
	* matches on egress_port
	* table_add control.table_name control.adjust_mac <port> => <srcAddr> <dstAddr>
	* control name has to be adjusted based on the pipeline structure
	*/
	table adjust_mac {
		key = {
			standard_metadata.egress_port: exact;
		}
		actions = {
			set_mac;
		}
	}

	apply {
		adjust_mac.apply();
	}
}