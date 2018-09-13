#![allow(dead_code)]

use futures::sync::mpsc::Receiver;
use client::Client;

pub struct HbbftAdapter {
	client: Client,
	block_rx: Receiver<u8>,
}

impl HbbftAdapter {

}


#[cfg(test)]
mod tests {

}