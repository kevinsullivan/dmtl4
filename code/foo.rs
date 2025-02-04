use std::io::{BufRead, BufReader, Read, Write}; // Added Write to the imports
use std::net::TcpStream;

fn main() {
    // The URL to fetch data from
    let url = "http://www.cs.utexas.edu/~scottm";

    // Split the URL into host and path
    let (host, path) = parse_url(url).expect("Failed to parse URL");

    // Create a TCP connection to the host
    let mut stream =
        TcpStream::connect(format!("{}:80", host)).expect("Failed to connect to server");

    // Build the HTTP GET request
    let request = format!(
        "GET {} HTTP/1.1\r\nHost: {}\r\nConnection: close\r\n\r\n",
        path, host
    );

    // Send the request to the server
    stream
        .write_all(request.as_bytes())
        .expect("Failed to send request");

    // Read the response from the server
    let mut reader = BufReader::new(&stream);
    let mut response = String::new();

    // Skip the HTTP headers until we reach an empty line (end of headers)
    loop {
        let mut line = String::new();
        let bytes_read = reader.read_line(&mut line).expect("Failed to read line");
        if bytes_read == 0 || line == "\r\n" {
            break;
        }
    }

    // Now read the body of the response
    reader
        .read_to_string(&mut response)
        .expect("Failed to read response body");

    // Count the number of tokens (words) in the response
    let mut count = 0;
    for token in response.split_whitespace() {
        println!("{}", token);
        count += 1;
    }

    // Print the total number of tokens
    println!("Number of tokens: {}", count);
}

// Helper function to parse the URL into host and path
fn parse_url(url: &str) -> Option<(&str, String)> {
    // Changed return type to include String
    if !url.starts_with("http://") {
        return None;
    }

    let rest = &url[7..]; // Remove "http://"
    let parts: Vec<&str> = rest.splitn(2, '/').collect();

    if parts.len() < 2 || parts[1].is_empty() {
        return Some((parts[0], "/".to_owned())); // Return "/" as a String
    }

    // Use format! to create a new String
    let path = format!("/{}", parts[1]);
    Some((parts[0], path)) // Return the path as a String
}
