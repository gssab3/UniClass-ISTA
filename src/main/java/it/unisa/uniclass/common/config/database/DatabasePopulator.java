package it.unisa.uniclass.common.config.database;

import it.unisa.uniclass.orari.model.AnnoDidattico; // <--- Importante: Import aggiunto
import it.unisa.uniclass.orari.model.Corso;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Ruolo;
import it.unisa.uniclass.utenti.model.Tipo;

import jakarta.annotation.PostConstruct;
import jakarta.ejb.Singleton;
import jakarta.ejb.Startup;
import jakarta.persistence.EntityManager;
import jakarta.persistence.PersistenceContext;

import java.time.LocalDate;

@Singleton
@Startup
public class DatabasePopulator {

    @PersistenceContext(unitName = "DBUniClassPU")
    private EntityManager em;

    @PostConstruct
    public void populateDB() {

        System.out.println("=== POPOLAMENTO DB AVVIATO ===");

        // ---------------------------
        // 0. ANNO DIDATTICO (Necessario per i corsi)
        // ---------------------------
        AnnoDidattico annoCorrente = new AnnoDidattico("2024/2025");
        em.persist(annoCorrente);

        // ---------------------------
        // 1. CORSO DI LAUREA
        // ---------------------------
        CorsoLaurea cl = new CorsoLaurea("Informatica");
        em.persist(cl);

        // ---------------------------
        // 2. DOCENTE
        // ---------------------------
        Accademico docente = new Accademico();
        docente.setEmail("docente.test@unisa.it");
        docente.setPassword("Test123%");
        docente.setNome("Mario");
        docente.setCognome("Rossi");
        docente.setDataNascita(LocalDate.of(1980, 1, 1));
        docente.setTelefono("3331112222");
        docente.setIscrizione(LocalDate.now());
        docente.setTipo(Tipo.Accademico);
        docente.setMatricola("D0001");
        docente.setRuolo(Ruolo.DOCENTE);
        docente.setDipartimento("Informatica");
        docente.setAttivato(true);
        em.persist(docente);

        // ---------------------------
        // 3. STUDENTE
        // ---------------------------
        Accademico studente = new Accademico();
        studente.setEmail("studente.test@unisa.it");
        studente.setPassword("Test123%");
        studente.setNome("Luca");
        studente.setCognome("Bianchi");
        studente.setDataNascita(LocalDate.of(2000, 1, 1));
        studente.setTelefono("3334445555");
        studente.setIscrizione(LocalDate.now());
        studente.setTipo(Tipo.Accademico);
        studente.setMatricola("S0001");
        studente.setRuolo(Ruolo.STUDENTE);
        studente.setDipartimento("Informatica");
        studente.setAttivato(true);
        studente.setCorsoLaurea(cl);
        em.persist(studente);

        // ---------------------------
        // 4. CORSI
        // ---------------------------
        Corso c1 = new Corso("Programmazione 1");
        c1.setCorsoLaurea(cl);
        c1.setAnnoDidattico(annoCorrente); // <--- FIX: Assegnazione anno
        em.persist(c1);

        Corso c2 = new Corso("Basi di Dati");
        c2.setCorsoLaurea(cl);
        c2.setAnnoDidattico(annoCorrente); // <--- FIX: Assegnazione anno
        em.persist(c2);

        Corso c3 = new Corso("Algoritmi");
        c3.setCorsoLaurea(cl);
        c3.setAnnoDidattico(annoCorrente); // <--- FIX: Assegnazione anno
        em.persist(c3);

        System.out.println("=== POPOLAMENTO DB COMPLETATO ===");
    }
}