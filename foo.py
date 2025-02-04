import requests
from bs4 import BeautifulSoup
import os

# Function to fetch and parse a webpage
def get_page_content(url):
    headers = {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/58.0.3029.110 Safari/537.3'}
    response = requests.get(url, headers=headers)
    
    if response.status_code == 200:
        return BeautifulSoup(response.content, 'html.parser')
    else:
        print(f"Failed to retrieve page: {url}")
        return None

# Function to extract blog post links from a page
def extract_blog_links(soup):
    blog_links = []
    articles = soup.find_all('article')  # Adjust this based on actual HTML structure
    
    for article in articles:
        link_tag = article.find('a', href=True)
        if link_tag:
            blog_links.append(link_tag['href'])
    
    return blog_links

# Function to extract blog post content
def extract_blog_post_content(post_url):
    soup = get_page_content(post_url)
    if not soup:
        return None

    title = soup.find('h1')  # Assuming the title is inside an <h1> tag
    content = soup.find('div', class_='blog-content')  # Adjust this based on actual HTML structure
    
    if title and content:
        return {
            'title': title.get_text(strip=True),
            'content': content.get_text(strip=True),
            'url': post_url
        }
    else:
        return None

# Main function to scrape all blog posts
def scrape_blog_posts(base_url, output_dir='blog_posts'):
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    page_num = 1
    while True:
        print(f"Scraping page {page_num}...")
        url = f"{base_url}?page={page_num}"  # Update this based on actual pagination structure
        soup = get_page_content(url)
        
        if not soup:
            break
        
        blog_links = extract_blog_links(soup)
        
        if not blog_links:
            print("No more blog posts found.")
            break
        
        for link in blog_links:
            full_link = link if link.startswith('http') else base_url + link
            post_data = extract_blog_post_content(full_link)
            
            if post_data:
                # Save the blog post to a text file
                filename = os.path.join(output_dir, f"{post_data['title'][:50]}.txt")  # Limit filename length
                with open(filename, 'w', encoding='utf-8') as f:
                    f.write(f"Title: {post_data['title']}\n")
                    f.write(f"URL: {post_data['url']}\n\n")
                    f.write(post_data['content'])
                print(f"Saved: {filename}")
        
        page_num += 1

if __name__ == "__main__":
    BASE_URL = "https://www.athenahealth.com/resources/blog"
    scrape_blog_posts(BASE_URL)