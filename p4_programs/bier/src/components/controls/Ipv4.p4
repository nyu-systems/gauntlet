/* Ipv4.p4 -*- c -*-
*
* This contorl unit applies layer 3 forwarding, adds bier(-te) layers and decaps
* ip packets
*/
control IPv4(inout headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata){

    /*
    * Forward ipv4 packet
    * Set egress port and change source & dst mac adress for correct layer 2 header
    * decrement ttl
    */
    action forward(egressSpec_t port) {
            standard_metadata.egress_spec = port;

            // decrement time to live (ttl)
            hdr.ipv4.ttl = hdr.ipv4.ttl - 1;
    }

    action decap() {
            hdr.ethernet.etherType = TYPE_BIER; // set ethertype according to argument
            hdr.ipv4.setInvalid(); // remove ipv4 header
            recirculate<metadata>(meta);
    }

     // encap ipv4 packet in bier
    action add_bier(bierBitmask bs) {
        hdr.bier.setValid(); // activate bier header
        hdr.bier.Proto = hdr.ethernet.etherType;
        hdr.bier.BitString = bs; // set bitstring

        hdr.ethernet.etherType = TYPE_BIER;

        // remove outer ipv4 layer and copy it to inner ipv4 header, workaround for (possible) later ip tunnel
        hdr.ipv4_inner = hdr.ipv4;
        hdr.ipv4.setInvalid();
        hdr.ipv4_inner.setValid();

        recirculate<metadata>(meta);
    }



    // table for ipv4 unicast match
    table ipv4 {
        key = {
            hdr.ipv4.dstAddr: lpm;
            meta.ports.status: ternary;
        }
        actions = {
            forward;
            decap;
        }
    }

    // set mc group for mc traffic
    action set_mc_grp(bit<16> grp) {
        standard_metadata.mcast_grp = grp;
    }

    table ipv4_mc {
        key = {
            hdr.ipv4.dstAddr: exact;
        }
        actions = {
            set_mc_grp;
        }
    }

    table encap_ipv4 {
        key = {
            hdr.ipv4.dstAddr: exact;
        }
        actions = {
            add_bier;
        }
    }


    // check if its a mc packet (hit from mc table) or just plain ipv4
    apply {

        //if(hdr.ipv4.flags != 2) { // set encap flag
        //    hdr.ipv4.flags = 1;
        //}

        if(hdr.igmp.isValid()) {
            standard_metadata.egress_spec = 16; // send to controller
        }
        else {
            ipv4.apply();

            if(standard_metadata.instance_type != PKT_INSTANCE_TYPE_INGRESS_RECIRC) { // a recirculated ip packet is a decaped mc packet
                encap_ipv4.apply();
            }
            else {
                ipv4_mc.apply(); // otherwise do normal mc stuff
            }

        }
    }
}
