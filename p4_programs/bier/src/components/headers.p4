#define PKT_INSTANCE_TYPE_NORMAL 0
#define PKT_INSTANCE_TYPE_INGRESS_CLONE 1
#define PKT_INSTANCE_TYPE_EGRESS_CLONE 2
#define PKT_INSTANCE_TYPE_COALESCED 3
#define PKT_INSTANCE_TYPE_INGRESS_RECIRC 4
#define PKT_INSTANCE_TYPE_REPLICATION 5
#define PKT_INSTANCE_TYPE_RESUBMIT 6
#define CONTROLLER_PORT 16
#define SEGMENT_WIDTH 8


// adress specification
typedef bit<9> egressSpec_t;
typedef bit<48> macAddr_t;
typedef bit<32> ip4Addr_t;
typedef bit<64> bierBitmask;

// proto numbers
const bit<16> TYPE_IPV4 = 0x800;
const bit<16> TYPE_BIER = 0xBB00;
const bit<16> TYPE_TOP_DISCOVER = 0xDD00;
const bit<8>  TYPE_IP_BIER = 0x8F;
const bit<8> TYPE_IP_IGMP = 0x2;


// Topology discovery header, proprietary
header topology_discover_t {
    bit<32> identifier;
    bit<16> port;
    bit<32> prefix;
    bit<48> mac;
}

// Ethernet header
header ethernet_t {
	macAddr_t dstAddr;
	macAddr_t srcAddr;
	bit<16> etherType;
}

// IP header
header ipv4_t {
    bit<4>    version;
    bit<4>    ihl;
    bit<8>    diffserv;
    bit<16>   totalLen;
    bit<16>   identification;
    bit<3>    flags;
    bit<13>   fragOffset;
    bit<8>    ttl;
    bit<8>    protocol;
    bit<16>   hdrChecksum;
    ip4Addr_t srcAddr;
    ip4Addr_t dstAddr;
}

// IGMP header for multicast subscription
header igmp_t {
    bit<8> typ;
    bit<8> max_response_time;
    bit<16> checksum;
    bit<32> mcast_addr;
}


/*
* BIER header based on the BIER MPLS encap draft:
* https://datatracker.ietf.org/doc/draft-ietf-bier-mpls-encapsulation/
* Only BitString, Proto and Bift-id (a.k.a. Domain) are used in this implementation
*/
header bier_t {
    // The bitstring of the header of length 64
    bit<64>   BitString;
    bit<16>   Proto;
    bit<24>   Domain;
}

// header naming
struct headers {
    ethernet_t          ethernet;
    ipv4_t              ipv4;
    igmp_t              igmp;
    bier_t              bier;
    ipv4_t              ipv4_inner;
    topology_discover_t topology;
}


// Metadata definition (local variables) for BIER forwarding
struct bier_metadata_t {
    // A bitstring/bitmask used in forwarding
    bit<64> remainingBits;
    bit<1> mdValid;
}

struct port_metadata_t {
    bit<8> status;
    bit<1> mdValid;
}


struct intrinsic_metadata_t {
    bit<48> ingress_global_timestamp;
    bit<48> egress_global_timestamp;
    bit<32> lf_field_list;
    bit<16> mcast_grp;
    bit<32> resubmit_flag;
    bit<16> egress_rid;
    bit<32> recirculate_flag;
}

// meta data instances
struct metadata {
    bier_metadata_t bier_md;
    port_metadata_t ports;
    intrinsic_metadata_t intrinsic_metadata;
}
