package it.unisa.uniclass.testing.unit.utenti.service.dao;

import it.unisa.uniclass.utenti.model.PersonaleTA;
import jakarta.persistence.EntityManager;
import jakarta.persistence.TypedQuery;
import jakarta.persistence.NoResultException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class PersonaleTADAOTest {

    private EntityManager em;
    private TypedQuery<PersonaleTA> personaleQuery;
    private PersonaleTADAO dao;

    @BeforeEach
    void setUp() {
        em = mock(EntityManager.class);
        personaleQuery = mock(TypedQuery.class);

        dao = new PersonaleTADAO();

        // Iniettiamo il mock dell'EntityManager via reflection
        try {
            var field = PersonaleTADAO.class.getDeclaredField("emUniClass");
            field.setAccessible(true);
            field.set(dao, em);
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    @Test
    void testTrovaPersonale() {
        PersonaleTA p = new PersonaleTA();
        when(em.createNamedQuery(PersonaleTA.TROVA_PERSONALE, PersonaleTA.class)).thenReturn(personaleQuery);
        when(personaleQuery.setParameter("id", 1L)).thenReturn(personaleQuery);
        when(personaleQuery.getSingleResult()).thenReturn(p);

        assertEquals(p, dao.trovaPersonale(1L));
    }

    @Test
    void testTrovaTutti() {
        List<PersonaleTA> list = Collections.singletonList(new PersonaleTA());
        when(em.createNamedQuery(PersonaleTA.TROVA_TUTTI, PersonaleTA.class)).thenReturn(personaleQuery);
        when(personaleQuery.getResultList()).thenReturn(list);

        assertEquals(list, dao.trovaTutti());
    }

    @Test
    void testTrovaEmail_Success() {
        PersonaleTA p = new PersonaleTA();
        when(em.createNamedQuery(PersonaleTA.TROVA_EMAIL, PersonaleTA.class)).thenReturn(personaleQuery);
        when(personaleQuery.setParameter("email", "x@y.com")).thenReturn(personaleQuery);
        when(personaleQuery.getSingleResult()).thenReturn(p);

        assertEquals(p, dao.trovaEmail("x@y.com"));
    }

    @Test
    void testTrovaEmail_NoResult() {
        when(em.createNamedQuery(PersonaleTA.TROVA_EMAIL, PersonaleTA.class)).thenReturn(personaleQuery);
        when(personaleQuery.setParameter("email", "x@y.com")).thenReturn(personaleQuery);
        when(personaleQuery.getSingleResult()).thenThrow(new NoResultException());

        assertNull(dao.trovaEmail("x@y.com"));
    }

    @Test
    void testTrovaEmailPassword_Success() {
        PersonaleTA p = new PersonaleTA();
        when(em.createNamedQuery(PersonaleTA.TROVA_EMAIL_PASSWORD, PersonaleTA.class)).thenReturn(personaleQuery);
        when(personaleQuery.setParameter("email", "x@y.com")).thenReturn(personaleQuery);
        when(personaleQuery.setParameter("password", "pwd")).thenReturn(personaleQuery);
        when(personaleQuery.getSingleResult()).thenReturn(p);

        assertEquals(p, dao.trovaEmailPassword("x@y.com", "pwd"));
    }

    @Test
    void testTrovaEmailPassword_NoResult() {
        when(em.createNamedQuery(PersonaleTA.TROVA_EMAIL_PASSWORD, PersonaleTA.class)).thenReturn(personaleQuery);
        when(personaleQuery.setParameter("email", "x@y.com")).thenReturn(personaleQuery);
        when(personaleQuery.setParameter("password", "pwd")).thenReturn(personaleQuery);
        when(personaleQuery.getSingleResult()).thenThrow(new NoResultException());

        assertNull(dao.trovaEmailPassword("x@y.com", "pwd"));
    }

    @Test
    void testAggiungiPersonale() {
        PersonaleTA p = new PersonaleTA();
        dao.aggiungiPersonale(p);
        verify(em).merge(p);
    }

    @Test
    void testRimuoviPersonale() {
        PersonaleTA p = new PersonaleTA();
        dao.rimuoviPersonale(p);
        verify(em).remove(p);
    }
}
