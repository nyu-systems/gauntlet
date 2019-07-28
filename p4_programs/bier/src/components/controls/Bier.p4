/*
* Control unit for BIER
* This control unit is heavily inspired by the demo of Wolfgang Braun and Joshua Hartman
*
* Copyright 2018 Steffen Lindner
*
* Licensed under the Apache License, Version 2.0 (the "License");
* you may not use this file except in compliance with the License.
* You may obtain a copy of the License at
*
*     http://www.apache.org/licenses/LICENSE-2.0
*
* Unless required by applicable law or agreed to in writing, software
* distributed under the License is distributed on an "AS IS" BASIS,
* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
* See the License for the specific language governing permissions and
* limitations under the License.
*/

control Bier(inout headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {


	/*************************************************************************
	***********************  Helper actions       ****************************
	*************************************************************************/


	/*
	* Clone the packet with meta data
	*/
	action clone_meta() {
		clone3<metadata>(CloneType.I2E, 1024, meta);
	}

	/*
	* Set meta data, i.e. set the remaining bits (= original packet bitstrings)
	* We can 'loop' over the remaining bits until there are no bits left
	*/
	action set_meta_data() {
		meta.bier_md.remainingBits = hdr.bier.BitString;
		meta.bier_md.mdValid = 1;
	}

	/*
	* Add ip header for FRR
	*/
	action add_ip_header(ip4Addr_t srcAddr, ip4Addr_t dstAddr) {
		hdr.ipv4.setValid(); // set outer ipv4 header
		hdr.ipv4.protocol = TYPE_IP_BIER; // set proto field to IP in IP tunnel (IP | Bier | IP)
		hdr.ethernet.etherType = TYPE_IPV4;
		hdr.ipv4.srcAddr = srcAddr;  // set src and dst Adress
		hdr.ipv4.dstAddr = dstAddr;  // for ip tunnel
	}

	/*************************************************************************
	***********************  Bier section   **********************************
	*************************************************************************/

	/*
 	* Forwards the BIER packet to one multicast child of this node according to
 	* https://datatracker.ietf.org/doc/draft-ietf-bier-architecture/
 	*/
	action forward(bierBitmask fbm, egressSpec_t port) {
		hdr.bier.BitString = hdr.bier.BitString & fbm; // keep only bits relevant for child
		standard_metadata.egress_spec = port; // set out port

		meta.bier_md.remainingBits = meta.bier_md.remainingBits & ~fbm;
		clone_meta(); // clone packet to egress and recirc for remaining bits in bitstring

	}

	/*
	* Encap bier packet in ip packet to build "backup path" for frr
	*/
	action forward_encap(bierBitmask fbm, ip4Addr_t srcAddr, ip4Addr_t dstAddr) {
		add_ip_header(srcAddr, dstAddr);

		meta.bier_md.remainingBits = meta.bier_md.remainingBits & ~fbm; // remove fbm used on the failed link

		clone_meta(); // clone packet to egress and recirc for remaining bits in bitstring

		recirculate<metadata>(meta); // recirculate to do normal IPv4 (tunnel)
	}

    action decap(bierBitmask decapBit) {
        hdr.ethernet.etherType = hdr.bier.Proto;
        hdr.bier.setInvalid(); // remove bier header

        meta.bier_md.remainingBits = meta.bier_md.remainingBits & ~decapBit; // for the case its a bier packet

        // activate ipv4 header
        hdr.ipv4.setValid();
        hdr.ipv4 = hdr.ipv4_inner; // copy original ipv4 header to outer header f
        hdr.ipv4_inner.setInvalid();

        clone_meta(); // thats the changed bier packet, without decap bit

        recirculate<metadata>(meta);  // thats the ipv4 mc packet
    }


	/*
	* BIER Bit Index Forwarding Table (BIFT)
	* Match on BitString and corresponding (outgoing) port
	*/
	table bift {
		key = {
			meta.bier_md.remainingBits: ternary;
			meta.ports.status: ternary;
		}
		actions = {
			forward;
			forward_encap;
            decap;
		}
	}


	apply {
		// set current meta data and live ports
		if(meta.bier_md.mdValid == 0) {
			set_meta_data();
		}

		// its a cloned packet and needs to be sliced
		if(standard_metadata.instance_type == PKT_INSTANCE_TYPE_INGRESS_CLONE) {

            // only recirculate when bit string is not empty
            if(meta.bier_md.remainingBits != 0) {
                recirculate<metadata>(meta);
            }

		} // otherwise do normal bift matching
		else {
			bift.apply();  // so apply normal bift
		}
	}
}
