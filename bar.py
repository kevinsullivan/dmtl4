import requests
from bs4 import BeautifulSoup
import time
import os

# Base URL of the blog
BASE_URL = 'https://www.athenahealth.com/resources/blog'

# Directory to save blog posts
SAVE_DIR = 'athenahealth_blog_posts'
os.makedirs(SAVE_DIR, exist_ok=True)

# Function to get the soup object of a page
def get_soup(url):
    response = requests.get(url)
    if response.status_code == 200:
        return BeautifulSoup(response.content, 'html.parser')
    else:
        print(f'Failed to retrieve {url}')
        return None

# Function to extract blog post links from a page
def get_blog_links(soup):
    links = []
    for article in soup.find_all('article'):
        a_tag = article.find('a', href=True)
        if a_tag:
            links.append(a_tag['href'])
    return links

# Function to download and save a blog post
def download_blog_post(url):
    soup = get_soup(url)
    if soup:
        title_tag = soup.find('h1')
        content_tag = soup.find('div', class_='blog-content')  # Adjust the class name as needed

        if title_tag and content_tag:
            title = title_tag.get_text(strip=True).replace('/', '-').replace('\\', '-')
            content = content_tag.get_text(separator='\n', strip=True)

            filename = os.path.join(SAVE_DIR, f"{title}.txt")
            with open(filename, 'w', encoding='utf-8') as f:
                f.write(f'Title: {title}\n\n')
                f.write(content)
            print(f'Saved: {title}')
        else:
            print(f'Failed to extract content from {url}')

# Main function to scrape all blog posts
def main():
    page = 0
    while True:
        url = f'{BASE_URL}?page={page}'
        soup = get_soup(url)
        if not soup:
            break

        blog_links = get_blog_links(soup)
        if not blog_links:
            print('No more blog posts found.')
            break

        for link in blog_links:
            full_url = f'https://www.athenahealth.com{link}'
            download_blog_post(full_url)
            time.sleep(2)  # Delay to avoid overloading the server

        page += 1
        time.sleep(2)

if __name__ == '__main__':
    main()
