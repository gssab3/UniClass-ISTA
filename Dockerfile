# Parto da jdk21
FROM eclipse-temurin:21-jdk


# Non essendoci delle build predefinite con TomEE 10, ne prendiamo una noi online
RUN curl -L https://downloads.apache.org/tomee/tomee-10.1.3/apache-tomee-10.1.3-microprofile.tar.gz -o /tmp/tomee.tar.gz \
    && tar -xzf /tmp/tomee.tar.gz -C /usr/local/ \
    && mv /usr/local/apache-tomee-microprofile-10.1.3 /usr/local/tomee \
    && rm /tmp/tomee.tar.gz



# Si copia il war nel target (grazie a mvn clean package) all'interno del container della webapp
COPY target/UniClass-Dependability.war /usr/local/tomee/webapps/UniClass-Dependability.war

# Si copiano i context e system.properties (che aggiungono info sulla Risorsa DB e Proprietà sul sistema blacklist/whitelist EJB) nel container webapp
COPY .smarttomcat/UniClass-Dependability/conf/context.xml /usr/local/tomee/conf/context.xml
COPY .smarttomcat/UniClass-Dependability/conf/system.properties /usr/local/tomee/conf/system.properties

# Utile per mettere in attesa tomEE per l'avvio del dbuniclass. Ottimo se il server non si riavvia automaticamente alla ricerca del driver attivo
# COPY wait-for-it.sh /wait-for-it.sh
# RUN chmod +x /wait-for-it.sh


# Va sulla porta 8080
EXPOSE 8080

CMD ["/usr/local/tomee/bin/catalina.sh", "run"]
